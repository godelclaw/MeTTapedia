import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup

/-!
# Finite-interface pumping on a decomposition tree

The corridor is one convenient decomposition, not the logical essence of the
descent.  What the descent actually needs is that the decomposition tree cannot
be deep: if a node and one of its proper descendants carry the same typed
interface state, the piece below the ancestor may be replaced by the piece below
the descendant, producing a strictly smaller counterexample.  Minimality
therefore forbids a repeated state along any root-to-leaf descent, and with
finitely many typed states that caps the depth, hence the node count, hence the
number of vertices.

Two facts carry the argument and both are proved here in full generality.

*No descent repeats a state.*  A descent is recorded as the list of labels met,
so ancestor--descendant comparability along it is just list order and needs no
separate argument.  If the states along a descent are pairwise distinct, the
descent is no longer than the number of states.

*A shallow binary tree is small.*  A rooted binary tree of depth `d` has at most
`2^d - 1` nodes.  The induction is stated in the equivalent form
`nodeCount + 1 ≤ 2 ^ depth`, which avoids truncated subtraction.

The replacement step itself is a hypothesis here, as it must be: it is where the
geometry lives.  This file supplies the finite-tree half.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FiniteTreeInterfacePumping

variable {α : Type*}

/-- A rooted binary decomposition tree whose nodes carry labels. -/
inductive DecompTree (α : Type*) where
  | tip : DecompTree α
  | node : α → DecompTree α → DecompTree α → DecompTree α
  deriving Inhabited

namespace DecompTree

/-- The number of labelled nodes. -/
def nodeCount : DecompTree α → ℕ
  | tip => 0
  | node _ l r => 1 + nodeCount l + nodeCount r

/-- The greatest number of nodes on a root-to-leaf descent. -/
def depth : DecompTree α → ℕ
  | tip => 0
  | node _ l r => 1 + max (depth l) (depth r)

/-- The labels met along one root-to-leaf descent, in order.  Because a descent
is recorded as a list, two of its nodes are automatically comparable. -/
inductive OnPath : DecompTree α → List α → Prop
  | tip : OnPath tip []
  | left {a : α} {l r : DecompTree α} {xs : List α} :
      OnPath l xs → OnPath (node a l r) (a :: xs)
  | right {a : α} {l r : DecompTree α} {xs : List α} :
      OnPath r xs → OnPath (node a l r) (a :: xs)

/-- Every tree has a descent realizing its depth. -/
theorem exists_deepest_path (t : DecompTree α) :
    ∃ p : List α, OnPath t p ∧ p.length = depth t := by
  induction t with
  | tip => exact ⟨[], OnPath.tip, rfl⟩
  | node a l r ihl ihr =>
      obtain ⟨pl, hpl, hlenl⟩ := ihl
      obtain ⟨pr, hpr, hlenr⟩ := ihr
      by_cases hcase : depth l ≤ depth r
      · refine ⟨a :: pr, OnPath.right hpr, ?_⟩
        simp [depth, hlenr, max_eq_right hcase, Nat.add_comm]
      · push_neg at hcase
        refine ⟨a :: pl, OnPath.left hpl, ?_⟩
        simp [depth, hlenl, max_eq_left (Nat.le_of_lt hcase), Nat.add_comm]

/-- **A shallow binary tree is small.**  Stated as `nodeCount + 1 ≤ 2 ^ depth`
to avoid truncated subtraction. -/
theorem nodeCount_succ_le_two_pow_depth (t : DecompTree α) :
    nodeCount t + 1 ≤ 2 ^ depth t := by
  induction t with
  | tip => simp [nodeCount, depth]
  | node a l r ihl ihr =>
      have hl : nodeCount l + 1 ≤ 2 ^ max (depth l) (depth r) :=
        ihl.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
      have hr : nodeCount r + 1 ≤ 2 ^ max (depth l) (depth r) :=
        ihr.trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
      have hpow : (2 : ℕ) ^ (1 + max (depth l) (depth r)) =
          2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) := by
        rw [Nat.add_comm, Nat.pow_succ]
        omega
      simp only [nodeCount, depth, hpow]
      omega

/-- The node count bound in the manuscript's displayed form. -/
theorem nodeCount_le (t : DecompTree α) : nodeCount t ≤ 2 ^ depth t - 1 := by
  have := nodeCount_succ_le_two_pow_depth t
  omega

end DecompTree

open DecompTree

variable {Q : Type*} [Fintype Q]

/-- **Minimality forbids a repeated typed state on a descent.**  This is the
hypothesis the replacement step supplies: two comparable nodes sharing a state
would splice to a strictly smaller counterexample. -/
def NoRepeatedStateOnDescents (state : α → Q) (t : DecompTree α) : Prop :=
  ∀ p : List α, OnPath t p → (p.map state).Nodup

/-- A descent with pairwise distinct states is no longer than the state set. -/
theorem path_length_le_card {state : α → Q} {p : List α}
    (hnodup : (p.map state).Nodup) : p.length ≤ Fintype.card Q := by
  simpa using hnodup.length_le_card

/-- **The depth bound.**  With `q` typed states and no repeat on any descent,
the tree has depth at most `q`. -/
theorem depth_le_card {state : α → Q} {t : DecompTree α}
    (hno : NoRepeatedStateOnDescents state t) : depth t ≤ Fintype.card Q := by
  obtain ⟨p, hpath, hlen⟩ := exists_deepest_path t
  exact hlen ▸ path_length_le_card (hno p hpath)

/-- **The node bound.** -/
theorem nodeCount_le_of_noRepeat {state : α → Q} {t : DecompTree α}
    (hno : NoRepeatedStateOnDescents state t) :
    nodeCount t ≤ 2 ^ Fintype.card Q - 1 := by
  have hdepth := depth_le_card hno
  have hmono : (2 : ℕ) ^ depth t ≤ 2 ^ Fintype.card Q :=
    Nat.pow_le_pow_right (by decide) hdepth
  have := nodeCount_succ_le_two_pow_depth t
  omega

/-- **Finite-interface pumping on a decomposition tree.**  If each node
introduces at most `c` vertices and every vertex is introduced exactly once,
then a minimal counterexample has at most `c(2^q - 1)` vertices.

The vertex accounting enters only through `hvertices`, which is Hypothesis 1 of
the manuscript: the total is at most `c` per node. -/
theorem vertexCount_le {state : α → Q} {t : DecompTree α}
    (hno : NoRepeatedStateOnDescents state t)
    (c vertexCount : ℕ) (hvertices : vertexCount ≤ c * nodeCount t) :
    vertexCount ≤ c * (2 ^ Fintype.card Q - 1) :=
  hvertices.trans (Nat.mul_le_mul_left c (nodeCount_le_of_noRepeat hno))

end GoertzelV24FiniteTreeInterfacePumping

end Mettapedia.GraphTheory.FourColor
