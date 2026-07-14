import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareComposition

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Adjacency in the line graph of the eight locally colored square-tangle
edges: four outer edges followed by the four square edges. -/
def SquareLineAdjProp (w : SquareBoundaryWord) (x : SquareInternalColoring)
    (a b : Color) (u v : SquareLocalNode) : Prop :=
  (SquareUndirectedEdge u v (squarePortalNode 0) (squareCornerNode 3) ∧
    IsTrackedColor a b (w 0) ∧ IsTrackedColor a b (x 3)) ∨
  (SquareUndirectedEdge u v (squarePortalNode 0) (squareCornerNode 0) ∧
    IsTrackedColor a b (w 0) ∧ IsTrackedColor a b (x 0)) ∨
  (SquareUndirectedEdge u v (squarePortalNode 1) (squareCornerNode 0) ∧
    IsTrackedColor a b (w 1) ∧ IsTrackedColor a b (x 0)) ∨
  (SquareUndirectedEdge u v (squarePortalNode 1) (squareCornerNode 1) ∧
    IsTrackedColor a b (w 1) ∧ IsTrackedColor a b (x 1)) ∨
  (SquareUndirectedEdge u v (squarePortalNode 2) (squareCornerNode 1) ∧
    IsTrackedColor a b (w 2) ∧ IsTrackedColor a b (x 1)) ∨
  (SquareUndirectedEdge u v (squarePortalNode 2) (squareCornerNode 2) ∧
    IsTrackedColor a b (w 2) ∧ IsTrackedColor a b (x 2)) ∨
  (SquareUndirectedEdge u v (squarePortalNode 3) (squareCornerNode 2) ∧
    IsTrackedColor a b (w 3) ∧ IsTrackedColor a b (x 2)) ∨
  (SquareUndirectedEdge u v (squarePortalNode 3) (squareCornerNode 3) ∧
    IsTrackedColor a b (w 3) ∧ IsTrackedColor a b (x 3)) ∨
  (SquareUndirectedEdge u v (squareCornerNode 0) (squareCornerNode 1) ∧
    IsTrackedColor a b (x 0) ∧ IsTrackedColor a b (x 1)) ∨
  (SquareUndirectedEdge u v (squareCornerNode 1) (squareCornerNode 2) ∧
    IsTrackedColor a b (x 1) ∧ IsTrackedColor a b (x 2)) ∨
  (SquareUndirectedEdge u v (squareCornerNode 2) (squareCornerNode 3) ∧
    IsTrackedColor a b (x 2) ∧ IsTrackedColor a b (x 3)) ∨
  (SquareUndirectedEdge u v (squareCornerNode 3) (squareCornerNode 0) ∧
    IsTrackedColor a b (x 3) ∧ IsTrackedColor a b (x 0))
  deriving Decidable

def SquareLineAdj (w : SquareBoundaryWord) (x : SquareInternalColoring)
    (a b : Color) (u v : SquareLocalNode) : Bool :=
  decide (SquareLineAdjProp w x a b u v)

theorem squareLineAdj_symm (w : SquareBoundaryWord)
    (x : SquareInternalColoring) (a b : Color) (u v : SquareLocalNode) :
    SquareLineAdj w x a b u v = SquareLineAdj w x a b v u := by
  apply Bool.decide_congr
  unfold SquareLineAdjProp SquareUndirectedEdge
  aesop

theorem squareLineAdj_self (w : SquareBoundaryWord)
    (x : SquareInternalColoring) (a b : Color) (u : SquareLocalNode) :
    SquareLineAdj w x a b u u = false := by
  simp only [SquareLineAdj, decide_eq_false_iff_not]
  fin_cases u <;>
    simp [SquareLineAdjProp, SquareUndirectedEdge,
      squarePortalNode, squareCornerNode]

/-- The tracked-color line graph of the eight local tangle edges. -/
def squareLineGraph (w : SquareBoundaryWord) (x : SquareInternalColoring)
    (a b : Color) : SimpleGraph SquareLocalNode where
  Adj u v := SquareLineAdj w x a b u v = true
  symm := ⟨by
    intro u v huv
    rw [squareLineAdj_symm w x a b u v] at huv
    exact huv⟩
  loopless := ⟨by
    intro u huu
    rw [squareLineAdj_self w x a b u] at huu
    contradiction⟩

/-- Portal connectivity computed in the local edge-line representation used
by the ambient Kempe graph. -/
def squareLineTrackedProfile (w : SquareBoundaryWord)
    (x : SquareInternalColoring) (a b : Color) : SquareTrackedProfile :=
  fun i j =>
    decide (IsTrackedColor a b (w i)) &&
    decide (IsTrackedColor a b (w j)) &&
    decide (squarePortalNode j ∈
      finsetReachWithin (SquareLineAdj w x a b) (squarePortalNode i) 8)

/-- The computed line profile is ordinary reachability in the local edge-line
graph. -/
theorem squareLineTrackedProfile_eq_true_iff
    (w : SquareBoundaryWord) (x : SquareInternalColoring)
    (a b : Color) (i j : Fin 4) :
    squareLineTrackedProfile w x a b i j = true ↔
      IsTrackedColor a b (w i) ∧ IsTrackedColor a b (w j) ∧
      (squareLineGraph w x a b).Reachable
        (squarePortalNode i) (squarePortalNode j) := by
  unfold squareLineTrackedProfile
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hreach :
      squarePortalNode j ∈
          finsetReachWithin (SquareLineAdj w x a b) (squarePortalNode i) 8 ↔
        (squareLineGraph w x a b).Reachable
          (squarePortalNode i) (squarePortalNode j) := by
    simpa using mem_finsetReachWithin_card_iff_reachable
      (squareLineGraph w x a b) (SquareLineAdj w x a b)
      (by intros; rfl) (squarePortalNode i) (squarePortalNode j)
  rw [hreach]
  tauto

private theorem squareLineProfile_eq_squareProfile_check :
    ∀ w : SquareBoundaryWord, ∀ a b : Color,
      a = 0 ∨ b = 0 ∨ a = b ∨
        (squareExtensions w).filter (fun x =>
          squareLineTrackedProfile w x a b = squareTrackedProfile w x a b) =
        squareExtensions w := by
  decide

/-- For every proper square extension and genuine tracked color pair, portal
connectivity in the original eight-node tangle equals portal connectivity in
its edge-line graph. This bridges the local table to the representation used
by rotation-system Kempe components. -/
theorem squareLineProfile_eq_squareProfile
    (w : SquareBoundaryWord) (x : SquareInternalColoring)
    (a b : Color) (hx : x ∈ squareExtensions w)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    squareLineTrackedProfile w x a b = squareTrackedProfile w x a b := by
  have hfilter :
      (squareExtensions w).filter (fun x =>
        squareLineTrackedProfile w x a b = squareTrackedProfile w x a b) =
      squareExtensions w := by
    rcases squareLineProfile_eq_squareProfile_check w a b with
      ha0 | hb0 | hab0 | h
    · exact False.elim (ha ha0)
    · exact False.elim (hb hb0)
    · exact False.elim (hab hab0)
    · exact h
  have hx' : x ∈ (squareExtensions w).filter (fun x =>
      squareLineTrackedProfile w x a b = squareTrackedProfile w x a b) := by
    rw [hfilter]
    exact hx
  exact (Finset.mem_filter.mp hx').2

end Mettapedia.GraphTheory.FourColor
