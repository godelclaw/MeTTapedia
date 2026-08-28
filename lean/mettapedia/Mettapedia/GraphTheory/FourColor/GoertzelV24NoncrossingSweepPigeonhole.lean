import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Vector

/-!
# Finite sweep states for bounded noncrossing stacks

Sweeping an ordered noncrossing partial matching exposes its open arcs in
last-in--first-out order.  If the nesting depth is at most `D`, one family
therefore contributes a word of length at most `D`, equivalently an element
of the finite sigma type `StackCode K D` below.

This file isolates the finite counting and pigeonhole part of the source's
length/depth alternative.  It deliberately does not claim that a graph-level
boundary construction supplies the noncrossing stacks: that is the separate
geometric input in M1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24NoncrossingSweepPigeonhole

open scoped BigOperators

universe u v

/-- A labelled stack of depth at most `D`, stored at its exact depth. -/
abbrev StackCode (K : Type u) (D : Nat) :=
  Σ d : Fin (D + 1), List.Vector K (d : Nat)

/-- The complete finite sweep state: one local letter and one bounded labelled
stack for each of `r` noncrossing families. -/
abbrev SweepState (A : Type u) (K : Type v) (r D : Nat) :=
  A × (Fin r → StackCode K D)

/-- A list whose length is bounded by `D` is exactly a `StackCode K D`.
This equivalence justifies using the sigma code as the literal stack carrier,
rather than merely as an upper bound. -/
def boundedListEquivStackCode (K : Type u) (D : Nat) :
    {items : List K // items.length ≤ D} ≃ StackCode K D where
  toFun items :=
    ⟨⟨items.1.length, Nat.lt_succ_iff.mpr items.2⟩, ⟨items.1, rfl⟩⟩
  invFun code :=
    ⟨code.2.1, by
      simpa [code.2.2] using Nat.le_of_lt_succ code.1.isLt⟩
  left_inv items := by
    apply Subtype.ext
    rfl
  right_inv code := by
    rcases code with ⟨⟨depth, hdepth⟩, ⟨items, hitems⟩⟩
    change items.length = depth at hitems
    subst depth
    rfl

noncomputable instance boundedListFintype [Fintype K] (D : Nat) :
    Fintype {items : List K // items.length ≤ D} :=
  Fintype.ofEquiv (StackCode K D) (boundedListEquivStackCode K D).symm

/-- Exact number of labelled stacks of depth at most `D`. -/
theorem card_stackCode [Fintype K] (D : Nat) :
    Fintype.card (StackCode K D) =
      ∑ d : Fin (D + 1), Fintype.card K ^ (d : Nat) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro depth _
  exact card_vector (α := K) (depth : Nat)

/-- Exact number of simultaneous bounded sweep states. -/
theorem card_sweepState [Fintype A] [Fintype K] (r D : Nat) :
    Fintype.card (SweepState A K r D) =
      Fintype.card A *
        (∑ d : Fin (D + 1), Fintype.card K ^ (d : Nat)) ^ r := by
  simp only [SweepState, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, card_stackCode]

/-- More cut positions than bounded sweep states force two distinct positions
with identical local letters and identical stacks in every family. -/
theorem exists_distinct_eq_sweepState
    [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    (r D n : Nat)
    (state : Fin n → SweepState A K r D)
    (hmany :
      Fintype.card A *
          (∑ d : Fin (D + 1), Fintype.card K ^ (d : Nat)) ^ r < n) :
    ∃ i j : Fin n, i ≠ j ∧ state i = state j := by
  have hcard : Fintype.card (SweepState A K r D) < Fintype.card (Fin n) := by
    simpa [card_sweepState] using hmany
  by_contra hno
  push Not at hno
  have hinjective : Function.Injective state := by
    intro i j hij
    by_contra hne
    exact hno i j hne hij
  have := Fintype.card_le_of_injective state hinjective
  omega

end GoertzelV24NoncrossingSweepPigeonhole

end Mettapedia.GraphTheory.FourColor
