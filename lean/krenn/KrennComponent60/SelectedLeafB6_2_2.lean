import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_2_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7b4a8c4e78c131245d382c01b70ce791d0ac01273af0b74bf8082675df30f921"
def certificateSHA256 : String := "4da36c822321c676b2fa5d90e28909e7be11746e9299dee42108f59feaa3f060"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 665 := ![
  11,
  12,
  22,
  25,
  144,
  145,
  147,
  165,
  172,
  178,
  179,
  194,
  264,
  292,
  293,
  294,
  295,
  300,
  301,
  302,
  308,
  367,
  383,
  434,
  436,
  443,
  464,
  470,
  556,
  578,
  579,
  655,
  656,
  657,
  658,
  661,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(11, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := -2, powers := [(19, 1), (27, 1), (47, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (22, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := -2, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (25, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(18, 1), (26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (32, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (19, 1), (27, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (20, 1), (25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (48, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (20, 1), (45, 1), (48, 1), (51, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (40, 1), (48, 1), (51, 1)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (45, 1), (48, 1), (51, 1)] }, { coefficient := -2, powers := [(20, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (20, 1), (29, 1), (48, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (32, 1), (48, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := -2, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (20, 1), (32, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (20, 1), (45, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (40, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (45, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := 2, powers := [(20, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(20, 1), (48, 1), (52, 1), (53, 1)] }, { coefficient := -2, powers := [(25, 1), (48, 1), (50, 1), (51, 1), (53, 1)] }, { coefficient := 2, powers := [(26, 1), (48, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (50, 1)] }]
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
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_2_2.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_2_2
