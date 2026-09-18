import Mettapedia.GraphTheory.Hypermap.Walkup.Basic

/-!
# What deleting a dart does to the three orbit counts

Deleting `z` removes one dart, and the node and face counts follow immediately
from `orbitCount_skipPerm`: each drops by one exactly when `z` was a fixed
point.  The edge count is the interesting one, and this module computes it.

## The edge permutation is the punctured one, twisted by a transposition

Write `σ` for the naive puncture `skipPerm H.edge z` — `edge` with `z` skipped.
When `z` is **degenerate** (fixed by one of the three permutations) Walkup's
edge permutation is exactly `σ`.  When it is not, the two differ at precisely
two darts, and the difference is a single transposition:

    (walkupE H z).edge = swap (edge z) (edge (node z)) * σ

That identity is the whole content of this module, because the tree already
knows what multiplying by a transposition does to an orbit count: it splits an
orbit in two when the transposed points share one, and merges two orbits into
one when they do not.  And the transposed points share a `σ`-cycle exactly when
`z` and `node z` share an `edge`-cycle — the **cross-edge** condition.

So:

* `z` degenerate: the edge count drops by one if `edge z = z`, else is unchanged;
* `z` non-degenerate and cross-edge: the edge count goes **up** by one (an edge
  cycle is cut in two);
* `z` non-degenerate and not cross-edge: it goes **down** by one (two edge
  cycles merge).

The source reaches the same three numbers through an adjunction over the region
swept out by the edge cycles of `z` and `node z`, together with three lemmas
about when two darts remain edge-connected after the transform.  All of that is
subsumed here by the transposition law, which this development already had.
-/

namespace Mettapedia.GraphTheory

open Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open Mettapedia.GraphTheory.OrbitCountSplitting

namespace Hypermap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Degeneracy and the cross-edge condition -/

/-- `z` is **degenerate** when one of the three permutations fixes it.  This is
the source's `glink z z`. -/
def Degenerate (H : Hypermap D) (z : D) : Prop :=
  H.edge z = z ∨ H.node z = z ∨ H.face z = z

/-- `z` is a **barb** when all three permutations fix it: an isolated dart. -/
def Barb (H : Hypermap D) (z : D) : Prop :=
  H.edge z = z ∧ H.node z = z ∧ H.face z = z

/-- **Cross-edge**: `z` and `node z` lie on one edge cycle.  This is exactly the
cycle that the transform cuts in two. -/
def CrossEdge (H : Hypermap D) (z : D) : Prop := H.edge.SameCycle z (H.node z)

/-! ### Any two fixed points force the third

The composite law makes the three fixed-point conditions two-out-of-three
dependent, so a degenerate non-barb dart is fixed by exactly one permutation. -/

theorem edge_fix_of_node_face {H : Hypermap D} {z : D}
    (hn : H.node z = z) (hf : H.face z = z) : H.edge z = z := by
  have h := H.cancel3 z
  have h1 : H.face (H.edge z) = z := H.node.injective (by rw [h, hn])
  exact H.face.injective (by rw [h1, hf])

theorem node_fix_of_edge_face {H : Hypermap D} {z : D}
    (he : H.edge z = z) (hf : H.face z = z) : H.node z = z := by
  have h := H.cancel3 z
  rwa [he, hf] at h

theorem face_fix_of_edge_node {H : Hypermap D} {z : D}
    (he : H.edge z = z) (hn : H.node z = z) : H.face z = z := by
  have h := H.cancel3 z
  rw [he] at h
  exact H.node.injective (by rw [h, hn])

/-! ## Two characterisations used throughout -/

theorem edge_eq_iff (H : Hypermap D) (z x : D) :
    H.edge x = z ↔ x = H.node (H.face z) := by
  constructor
  · intro h
    have := H.cancel3 x
    rw [h] at this
    exact this.symm
  · rintro rfl
    exact edge_node_face H z

theorem face_edge_eq_iff (H : Hypermap D) (z x : D) :
    H.face (H.edge x) = z ↔ x = H.node z := by
  rw [face_eq_iff H z (H.edge x)]
  constructor
  · exact fun h => H.edge.injective h
  · rintro rfl; rfl

/-! ## Walkup's edge formula, rewritten

Once `edge z ≠ z` the two nested conditions in `skipEdgeFun` are conditions on
`x` alone: the first says `x` is `node z`, the second that `x` is the edge
predecessor of `z`. -/

theorem skipEdgeFun_of_edge_ne (H : Hypermap D) (z : D) (hez : H.edge z ≠ z) (x : D) :
    skipEdgeFun H z x =
      if x = H.node z then H.edge z
      else if x = H.node (H.face z) then H.edge (H.node z)
      else H.edge x := by
  unfold skipEdgeFun
  rw [if_neg hez]
  by_cases h1 : x = H.node z
  · rw [if_pos ((face_edge_eq_iff H z x).2 h1), if_pos h1]
  · rw [if_neg (fun hc => h1 ((face_edge_eq_iff H z x).1 hc)), if_neg h1]
    by_cases h2 : x = H.node (H.face z)
    · rw [if_pos ((edge_eq_iff H z x).2 h2), if_pos h2]
    · rw [if_neg (fun hc => h2 ((edge_eq_iff H z x).1 hc)), if_neg h2]

/-! ## The degenerate case: the transform is the naive puncture

This is the source's `glink_fp_skip_edge`. -/

theorem skipEdgeFun_eq_skipFun_of_degenerate (H : Hypermap D) (z : D)
    (hd : Degenerate H z) (x : D) : skipEdgeFun H z x = skipFun H.edge z x := by
  unfold skipFun
  by_cases hez : H.edge z = z
  · -- Walkup's first branch fires, and the naive puncture agrees either way
    unfold skipEdgeFun
    rw [if_pos hez]
    by_cases hx : H.edge x = z
    · rw [if_pos hx, hez, hx]
    · rw [if_neg hx]
  · rw [skipEdgeFun_of_edge_ne H z hez]
    rcases hd with h | h | h
    · exact absurd h hez
    · -- `node z = z`: the first branch's target and the fallback coincide
      rw [h]
      by_cases hx : x = z
      · subst hx
        split_ifs <;> rfl
      · rw [if_neg hx]
        by_cases hx2 : x = H.node (H.face z)
        · rw [if_pos hx2, if_pos ((edge_eq_iff H z x).2 hx2)]
        · rw [if_neg hx2, if_neg (fun hc => hx2 ((edge_eq_iff H z x).1 hc))]
    · -- `face z = z`: the two conditions on `x` become the same condition
      have hsame : H.node (H.face z) = H.node z := by rw [h]
      rw [hsame]
      by_cases hx : x = H.node z
      · rw [if_pos hx, if_pos ((edge_eq_iff H z x).2 (by rw [hsame]; exact hx))]
      · rw [if_neg hx, if_neg hx,
          if_neg (fun hc => hx (by rw [(edge_eq_iff H z x).1 hc, hsame]))]

theorem walkupE_edge_of_degenerate (H : Hypermap D) (z : D) (hd : Degenerate H z) :
    (walkupE H z).edge = skipPerm H.edge z := by
  refine Equiv.ext fun u => Subtype.ext ?_
  rw [walkupE_edge_apply, skipPerm_apply_val]
  exact skipEdgeFun_eq_skipFun_of_degenerate H z hd (u : D)

/-! ## The non-degenerate case: a transposition twist

Three darts are in play: `edge z`, `edge (node z)`, and the edge predecessor
`node (face z)` of `z`.  Non-degeneracy keeps all of them away from `z` and
keeps the first two distinct. -/

section NonDegenerate

variable {H : Hypermap D} {z : D}

theorem edge_ne_of_not_degenerate (hd : ¬ Degenerate H z) : H.edge z ≠ z :=
  fun h => hd (Or.inl h)

theorem node_ne_of_not_degenerate (hd : ¬ Degenerate H z) : H.node z ≠ z :=
  fun h => hd (Or.inr (Or.inl h))

theorem face_ne_of_not_degenerate (hd : ¬ Degenerate H z) : H.face z ≠ z :=
  fun h => hd (Or.inr (Or.inr h))

/-- The edge predecessor of `z` survives the deletion. -/
theorem pred_ne_of_not_degenerate (hd : ¬ Degenerate H z) : H.node (H.face z) ≠ z := by
  intro h
  apply edge_ne_of_not_degenerate hd
  have hstep := edge_node_face H z
  rwa [h] at hstep

/-- The edge predecessor of `z` is not `node z`: that would make `z` a face
fixed point. -/
theorem pred_ne_node (hd : ¬ Degenerate H z) : H.node (H.face z) ≠ H.node z :=
  fun h => face_ne_of_not_degenerate hd (H.node.injective h)

theorem edge_node_ne (hd : ¬ Degenerate H z) : H.edge (H.node z) ≠ z :=
  fun h => pred_ne_node hd ((edge_eq_iff H z (H.node z)).1 h).symm

/-- **The twist.**  Off `z`, Walkup's edge permutation is the naive puncture
composed with the transposition of `edge z` and `edge (node z)`. -/
theorem walkupE_edge_eq_swap_mul (hd : ¬ Degenerate H z) :
    (walkupE H z).edge
      = Equiv.swap (⟨H.edge z, edge_ne_of_not_degenerate hd⟩ : {x : D // x ≠ z})
          ⟨H.edge (H.node z), edge_node_ne hd⟩ * skipPerm H.edge z := by
  have hez := edge_ne_of_not_degenerate hd
  have henz := edge_node_ne hd
  refine Equiv.ext fun u => Subtype.ext ?_
  set x : D := (u : D) with hx
  rw [walkupE_edge_apply, skipEdgeFun_of_edge_ne H z hez, Perm.mul_apply]
  by_cases h1 : x = H.node z
  · -- the puncture sends `node z` to `edge (node z)`, which the swap sends back
    have hval : ((skipPerm H.edge z u : {y : D // y ≠ z}) : D) = H.edge (H.node z) := by
      rw [skipPerm_apply_val, ← hx, h1, skipFun_of_ne henz]
    have : (skipPerm H.edge z u) = (⟨H.edge (H.node z), henz⟩ : {y : D // y ≠ z}) :=
      Subtype.ext hval
    rw [if_pos h1, this, Equiv.swap_apply_right]
  · by_cases h2 : x = H.node (H.face z)
    · -- the puncture sends the predecessor of `z` to `edge z`
      have hz : H.edge x = z := (edge_eq_iff H z x).2 h2
      have hval : ((skipPerm H.edge z u : {y : D // y ≠ z}) : D) = H.edge z := by
        rw [skipPerm_apply_val, ← hx, skipFun_of_eq hz]
      have : (skipPerm H.edge z u) = (⟨H.edge z, hez⟩ : {y : D // y ≠ z}) := Subtype.ext hval
      rw [if_neg h1, if_pos h2, this, Equiv.swap_apply_left]
    · -- elsewhere neither the puncture nor the swap does anything
      have hz : H.edge x ≠ z := fun hc => h2 ((edge_eq_iff H z x).1 hc)
      have hval : ((skipPerm H.edge z u : {y : D // y ≠ z}) : D) = H.edge x := by
        rw [skipPerm_apply_val, ← hx, skipFun_of_ne hz]
      have hne1 : (skipPerm H.edge z u) ≠ (⟨H.edge z, hez⟩ : {y : D // y ≠ z}) := by
        intro hc
        have : H.edge x = H.edge z := by rw [← hval, hc]
        exact u.2 (hx ▸ H.edge.injective this)
      have hne2 : (skipPerm H.edge z u) ≠ (⟨H.edge (H.node z), henz⟩ : {y : D // y ≠ z}) := by
        intro hc
        have : H.edge x = H.edge (H.node z) := by rw [← hval, hc]
        exact h1 (H.edge.injective this)
      rw [if_neg h1, if_neg h2, Equiv.swap_apply_of_ne_of_ne hne1 hne2, hval]

/-- The transposed darts share a punctured edge cycle exactly under the
cross-edge condition. -/
theorem sameCycle_swap_points_iff (hd : ¬ Degenerate H z) :
    (skipPerm H.edge z).SameCycle
        (⟨H.edge z, edge_ne_of_not_degenerate hd⟩ : {x : D // x ≠ z})
        ⟨H.edge (H.node z), edge_node_ne hd⟩
      ↔ CrossEdge H z := by
  rw [sameCycle_skipPerm_iff]
  constructor
  · intro h
    exact ((sameCycle_step H.edge z).trans h).trans (sameCycle_step H.edge (H.node z)).symm
  · intro h
    exact ((sameCycle_step H.edge z).symm.trans h).trans (sameCycle_step H.edge (H.node z))

end NonDegenerate

/-! ## The three edge counts -/

/-- Degenerate deletion: the edge count behaves like a plain puncture. -/
theorem orbitCount_walkupE_edge_of_degenerate (H : Hypermap D) (z : D) (hd : Degenerate H z) :
    (if H.edge z = z then 1 else 0) + orbitCount (walkupE H z).edge = orbitCount H.edge := by
  rw [walkupE_edge_of_degenerate H z hd]
  exact orbitCount_skipPerm H.edge z

/-- **Cross-edge deletion splits an edge cycle.** -/
theorem orbitCount_walkupE_edge_of_crossEdge (H : Hypermap D) (z : D)
    (hd : ¬ Degenerate H z) (hc : CrossEdge H z) :
    orbitCount (walkupE H z).edge = orbitCount H.edge + 1 := by
  have hez := edge_ne_of_not_degenerate hd
  have hne : (⟨H.edge z, hez⟩ : {x : D // x ≠ z}) ≠ ⟨H.edge (H.node z), edge_node_ne hd⟩ := by
    intro hcon
    exact node_ne_of_not_degenerate hd
      (H.edge.injective (congrArg Subtype.val hcon)).symm
  have hsplit := orbitCount_swap_mul_of_sameCycle (skipPerm H.edge z) hne
    ((sameCycle_swap_points_iff hd).2 hc)
  rw [walkupE_edge_eq_swap_mul hd, hsplit]
  have hskip := orbitCount_skipPerm H.edge z
  rw [if_neg hez] at hskip
  omega

/-- **Non-cross-edge deletion merges two edge cycles.** -/
theorem orbitCount_walkupE_edge_of_not_crossEdge (H : Hypermap D) (z : D)
    (hd : ¬ Degenerate H z) (hc : ¬ CrossEdge H z) :
    orbitCount (walkupE H z).edge + 1 = orbitCount H.edge := by
  have hez := edge_ne_of_not_degenerate hd
  have hne : (⟨H.edge z, hez⟩ : {x : D // x ≠ z}) ≠ ⟨H.edge (H.node z), edge_node_ne hd⟩ := by
    intro hcon
    exact node_ne_of_not_degenerate hd
      (H.edge.injective (congrArg Subtype.val hcon)).symm
  have hmerge := orbitCount_swap_mul_of_not_sameCycle (skipPerm H.edge z) hne
    (fun h => hc ((sameCycle_swap_points_iff hd).1 h))
  rw [walkupE_edge_eq_swap_mul hd]
  have hskip := orbitCount_skipPerm H.edge z
  rw [if_neg hez] at hskip
  omega

/-! ## The node and face counts -/

theorem orbitCount_walkupE_node (H : Hypermap D) (z : D) :
    (if H.node z = z then 1 else 0) + orbitCount (walkupE H z).node = orbitCount H.node :=
  orbitCount_skipPerm H.node z

theorem orbitCount_walkupE_face (H : Hypermap D) (z : D) :
    (if H.face z = z then 1 else 0) + orbitCount (walkupE H z).face = orbitCount H.face :=
  orbitCount_skipPerm H.face z

/-! ## The orbit total

Collecting the three counts.  The weight on the left is the number of orbits the
transform absorbs, and the case split below is the one the genus argument
consumes. -/

/-- In the degenerate case the orbit total drops by exactly one more than the
number of permutations fixing `z`, less one. -/
theorem eulerLhs_walkupE_of_degenerate (H : Hypermap D) (z : D) (hd : Degenerate H z) :
    ((if H.edge z = z then 1 else 0) + (if H.node z = z then 1 else 0)
      + (if H.face z = z then 1 else 0)) + eulerLhs (walkupE H z) = eulerLhs H := by
  have he := orbitCount_walkupE_edge_of_degenerate H z hd
  have hn := orbitCount_walkupE_node H z
  have hf := orbitCount_walkupE_face H z
  show _ + (orbitCount (walkupE H z).edge + orbitCount (walkupE H z).node
    + orbitCount (walkupE H z).face) = orbitCount H.edge + orbitCount H.node + orbitCount H.face
  omega

/-- Non-degenerate cross-edge deletion: the orbit total goes up by one. -/
theorem eulerLhs_walkupE_of_crossEdge (H : Hypermap D) (z : D)
    (hd : ¬ Degenerate H z) (hc : CrossEdge H z) :
    eulerLhs (walkupE H z) = eulerLhs H + 1 := by
  have he := orbitCount_walkupE_edge_of_crossEdge H z hd hc
  have hn := orbitCount_walkupE_node H z
  have hf := orbitCount_walkupE_face H z
  rw [if_neg (node_ne_of_not_degenerate hd)] at hn
  rw [if_neg (face_ne_of_not_degenerate hd)] at hf
  show orbitCount (walkupE H z).edge + orbitCount (walkupE H z).node
    + orbitCount (walkupE H z).face = orbitCount H.edge + orbitCount H.node + orbitCount H.face + 1
  omega

/-- Non-degenerate non-cross-edge deletion: the orbit total goes down by one. -/
theorem eulerLhs_walkupE_of_not_crossEdge (H : Hypermap D) (z : D)
    (hd : ¬ Degenerate H z) (hc : ¬ CrossEdge H z) :
    eulerLhs (walkupE H z) + 1 = eulerLhs H := by
  have he := orbitCount_walkupE_edge_of_not_crossEdge H z hd hc
  have hn := orbitCount_walkupE_node H z
  have hf := orbitCount_walkupE_face H z
  rw [if_neg (node_ne_of_not_degenerate hd)] at hn
  rw [if_neg (face_ne_of_not_degenerate hd)] at hf
  show orbitCount (walkupE H z).edge + orbitCount (walkupE H z).node
    + orbitCount (walkupE H z).face + 1
      = orbitCount H.edge + orbitCount H.node + orbitCount H.face
  omega

end Hypermap

end Mettapedia.GraphTheory
