import MettapediaFourColor.NearLinearDiamondData
import MettapediaFourColor.KempeBoundarySplit
import MettapediaFourColor.PatchWitness

/-!
# A boundary-collapse obstruction on a common five-triangle core

D0092 and D0063 are copied from near-linear-4ct/reducible-configurations,
revision c2ce7a96e35256201526e2abb51a39d04a588b53, copyright 2026
Yuta Inoue (MIT). The source files and licence are retained under
`tools/fourcolor/near-linear`.

A genuine D0092 colouring has a proper split trace whose collapse cannot
extend to D0063 at the stated boundary alignment. Three target core vertices
would form a triangle using only two colours. This refutes that reconstruction
contract, not D-reducibility or the possibility of a different repair law.
-/

namespace FourColor.FiveTriangleCollapseObstruction

open Color NearLinearDiamondData KempeBoundarySplit

set_option maxRecDepth 32768

def upper : Input 18 11 where
  source := "18 11\n\
    12 6 9 17 18 16 13 15\n\
    13 7 5 6 14 15 12 16 4\n\
    14 5 7 8 15 13 6\n\
    15 5 9 12 13 14 8\n\
    16 6 3 4 13 12 18 2\n\
    17 5 10 11 18 12 9\n\
    18 6 2 16 12 17 11 1\n\
    "
  valid := by decide +kernel

def lower : Input 17 10 where
  source := "17 10\n\
    11 6 9 10 17 14 15 8\n\
    12 5 5 13 15 16 4\n\
    13 5 6 7 15 12 5\n\
    14 5 16 15 11 17 2\n\
    15 7 8 11 14 16 12 13 7\n\
    16 6 3 4 12 15 14 2\n\
    17 5 2 14 11 10 1\n\
    "
  valid := by decide +kernel

def assignment : Fin 18 → Color :=
  ![c0, c1, c3, c1, c3, c1, c0, c1, c3, c2, c3, c1, c2, c3, c0, c0, c0, c2]

theorem assignment_proper : ∀ u v, upper.graph.Adj u v → assignment u ≠ assignment v := by
  decide +kernel

def colouring : upper.graph.Coloring Color := .mk assignment (fun h => assignment_proper _ _ h)

def tail : List Color := [c2, c2, c2, c1, c1, c2, c1, c1, c3]
def boundaryColors : List Color := [c0, c3, c1, c3, c1, c0, c1, c3, c2, c3]

theorem upper_witness : GraphTrace upper.graph upper.boundary (c1 :: c2 :: tail) := by
  exact ⟨colouring, by decide +kernel⟩

theorem boundary_trace : trace boundaryColors = (c1 + c2) :: tail := by rfl

private theorem triangle_two_colors (s a b c : Color)
    (a1 : a ≠ s + c1) (a3 : a ≠ s + c3)
    (b1 : b ≠ s + c1) (b3 : b ≠ s + c3)
    (c1' : c ≠ s + c1) (c3' : c ≠ s + c3)
    (ab : a ≠ b) (bc : b ≠ c) (ca : c ≠ a) : False := by
  revert a1 a3 b1 b3 c1' c3' ab bc ca
  revert s a b c
  decide +kernel

/-- A target colouring with this trace would two-colour a triangle. -/
theorem lower_obstruction : ¬ GraphTrace lower.graph lower.boundary ((c1 + c2) :: tail) := by
  rintro ⟨k, hk⟩
  have hlen : boundaryColors.length = (lower.boundary.map k).length := by
    simp [boundaryColors, Input.boundary, lower]
  have ht : trace boundaryColors = trace (lower.boundary.map k) := boundary_trace.trans hk
  have hs := ringColors_eq_shift hlen ht
  let s := boundaryColors.headD 0 + (lower.boundary.map k).headD 0
  change lower.boundary.map k = boundaryColors.map (s + ·) at hs
  have h2 : k 1 = s + c3 := by
    have h := congrArg (fun l => l.getD 1 c0) hs
    change k 1 = s + c3 at h
    exact h
  have h3 : k 2 = s + c1 := by
    have h := congrArg (fun l => l.getD 2 c0) hs
    change k 2 = s + c1 at h
    exact h
  have h4 : k 3 = s + c3 := by
    have h := congrArg (fun l => l.getD 3 c0) hs
    change k 3 = s + c3 at h
    exact h
  have h5 : k 4 = s + c1 := by
    have h := congrArg (fun l => l.getD 4 c0) hs
    change k 4 = s + c1 at h
    exact h
  have h7 : k 6 = s + c1 := by
    have h := congrArg (fun l => l.getD 6 c0) hs
    change k 6 = s + c1 at h
    exact h
  have h8 : k 7 = s + c3 := by
    have h := congrArg (fun l => l.getD 7 c0) hs
    change k 7 = s + c3 at h
    exact h
  apply triangle_two_colors s (k 11) (k 14) (k 15)
  · rw [← h5]; exact k.valid (by decide +kernel)
  · rw [← h4]; exact k.valid (by decide +kernel)
  · rw [← h7]; exact k.valid (by decide +kernel)
  · rw [← h8]; exact k.valid (by decide +kernel)
  · rw [← h3]; exact k.valid (by decide +kernel)
  · rw [← h2]; exact k.valid (by decide +kernel)
  · exact k.valid (by decide +kernel)
  · exact k.valid (by decide +kernel)
  · exact k.valid (by decide +kernel)

/-- The fixed-alignment reconstruction hypothesis of `repairs_collapse` fails. -/
theorem no_collapse_reconstruction :
    ¬ (∀ a b t, a ≠ (0 : Color) → b ≠ 0 → a ≠ b →
      GraphTrace upper.graph upper.boundary (a :: b :: t) →
      GraphTrace lower.graph lower.boundary ((a + b) :: t)) := by
  intro reconstruct
  exact lower_obstruction (reconstruct c1 c2 tail (by decide) (by decide)
    (by decide) upper_witness)

end FourColor.FiveTriangleCollapseObstruction
