import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Relator

/-!
# Sections of path-shaped constraint systems

A finite path of binary constraints may have a different state type at every
node.  If every edge relation is right-total, then an arbitrary terminal state
extends backwards to a section of the whole path.

This is the elementary acyclic constraint-satisfaction principle.  Unlike
pairwise or global consistency statements for a general constraint graph, it
uses only the absence of cycles in the indexing path.
-/

namespace Mettapedia.Logic

universe u

/-- A simultaneous assignment satisfying every edge of a finite path of
possibly dependent state types. -/
structure PathConstraint.Section {n : Nat}
    (State : Fin (n + 1) → Type u)
    (Compatible : (i : Fin n) → State i.castSucc → State i.succ → Prop) where
  state : (i : Fin (n + 1)) → State i
  compatible : ∀ i : Fin n, Compatible i (state i.castSucc) (state i.succ)

namespace PathConstraint

/-- Choose a path section backwards from a prescribed terminal state. -/
noncomputable def backwardChoice {n : Nat}
    (State : Fin (n + 1) → Type u)
    (Compatible : (i : Fin n) → State i.castSucc → State i.succ → Prop)
    (hRightTotal : ∀ i : Fin n, Relator.RightTotal (Compatible i))
    (terminal : State (Fin.last n)) :
    (i : Fin (n + 1)) → State i :=
  Fin.reverseInduction terminal
    (fun i target ↦ Classical.choose (hRightTotal i target))

@[simp] theorem backwardChoice_last {n : Nat}
    (State : Fin (n + 1) → Type u)
    (Compatible : (i : Fin n) → State i.castSucc → State i.succ → Prop)
    (hRightTotal : ∀ i : Fin n, Relator.RightTotal (Compatible i))
    (terminal : State (Fin.last n)) :
    backwardChoice State Compatible hRightTotal terminal (Fin.last n) = terminal := by
  simp [backwardChoice]

theorem backwardChoice_compatible {n : Nat}
    (State : Fin (n + 1) → Type u)
    (Compatible : (i : Fin n) → State i.castSucc → State i.succ → Prop)
    (hRightTotal : ∀ i : Fin n, Relator.RightTotal (Compatible i))
    (terminal : State (Fin.last n)) (i : Fin n) :
    Compatible i
      (backwardChoice State Compatible hRightTotal terminal i.castSucc)
      (backwardChoice State Compatible hRightTotal terminal i.succ) := by
  simp [backwardChoice]
  exact Classical.choose_spec (hRightTotal i
    (Fin.reverseInduction terminal
      (fun j target ↦ Classical.choose (hRightTotal j target)) i.succ))

/-- Right-totality of each edge constraint produces a section ending at any
prescribed state of the final node. -/
noncomputable def sectionEndingAt {n : Nat}
    (State : Fin (n + 1) → Type u)
    (Compatible : (i : Fin n) → State i.castSucc → State i.succ → Prop)
    (hRightTotal : ∀ i : Fin n, Relator.RightTotal (Compatible i))
    (terminal : State (Fin.last n)) : Section State Compatible where
  state := backwardChoice State Compatible hRightTotal terminal
  compatible := backwardChoice_compatible State Compatible hRightTotal terminal

@[simp] theorem sectionEndingAt_last {n : Nat}
    (State : Fin (n + 1) → Type u)
    (Compatible : (i : Fin n) → State i.castSucc → State i.succ → Prop)
    (hRightTotal : ∀ i : Fin n, Relator.RightTotal (Compatible i))
    (terminal : State (Fin.last n)) :
    (sectionEndingAt State Compatible hRightTotal terminal).state (Fin.last n) =
      terminal :=
  backwardChoice_last State Compatible hRightTotal terminal

/-- A value which is unchanged across every adjacent edge of a finite path is
equal to its value at the final node. -/
theorem value_eq_last_of_adjacent_eq {n : Nat} {Value : Type*}
    (value : Fin (n + 1) → Value)
    (hadjacent : ∀ i : Fin n, value i.castSucc = value i.succ)
    (index : Fin (n + 1)) :
    value index = value (Fin.last n) := by
  induction index using Fin.reverseInduction with
  | last => rfl
  | cast index ih => exact (hadjacent index).trans ih

/-- If two values on a finite path differ, some adjacent pair already
differs.  This is the local witness form of pathwise constancy. -/
theorem exists_adjacent_ne_of_ne {n : Nat} {Value : Type*}
    (value : Fin (n + 1) → Value) {first second : Fin (n + 1)}
    (hne : value first ≠ value second) :
    ∃ index : Fin n, value index.castSucc ≠ value index.succ := by
  classical
  by_contra hno
  have hadjacent : ∀ index : Fin n,
      value index.castSucc = value index.succ := by
    intro index
    by_contra hindex
    exact hno ⟨index, hindex⟩
  apply hne
  exact (value_eq_last_of_adjacent_eq value hadjacent first).trans
    (value_eq_last_of_adjacent_eq value hadjacent second).symm

/-- Observations respected by every compatibility constraint are constant on
any path section. -/
theorem section_observe_eq_last {n : Nat}
    {State : Fin (n + 1) → Type u}
    {Compatible : (i : Fin n) → State i.castSucc → State i.succ → Prop}
    (pathSection : Section State Compatible)
    {Value : Type*} (observe : (i : Fin (n + 1)) → State i → Value)
    (hobserve : ∀ (i : Fin n) (source : State i.castSucc)
      (target : State i.succ),
      Compatible i source target →
        observe i.castSucc source = observe i.succ target)
    (index : Fin (n + 1)) :
    observe index (pathSection.state index) =
      observe (Fin.last n) (pathSection.state (Fin.last n)) := by
  exact value_eq_last_of_adjacent_eq
    (fun i ↦ observe i (pathSection.state i))
    (fun i ↦ hobserve i _ _ (pathSection.compatible i))
    index

end PathConstraint

end Mettapedia.Logic
