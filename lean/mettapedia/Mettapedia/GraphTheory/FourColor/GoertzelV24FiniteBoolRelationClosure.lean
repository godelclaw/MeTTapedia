import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation

/-!
# Exact finite closure of a Boolean relation

The finite transfer layer stores local steps as Boolean tables.  This module
computes their directed reflexive-transitive closure by saturating a finite set
of seen vertices.  The main theorem is an exact `iff` with
`Relation.ReflTransGen`; in particular, no symmetry of the step relation is
assumed.

This is generic finite computational infrastructure.  It does not choose a
source alphabet, assert realizability of an encoded state, or perform a base
audit.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FiniteBoolRelationClosure

universe u

/-- Add every vertex reached by one directed Boolean step from the current
finite set. -/
def boolRelationExpansion {α : Type u} [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (seen : Finset α) : Finset α :=
  seen ∪ Finset.univ.filter fun target =>
    ∃ current ∈ seen, step current target = true

/-- Saturate until a fixed point is found or the supplied finite fuel is
exhausted. -/
def closeBoolRelationAux {α : Type u} [Fintype α] [DecidableEq α]
    (step : α → α → Bool) : Nat → Finset α → Finset α
  | 0, seen => seen
  | fuel + 1, seen =>
      let next := boolRelationExpansion step seen
      if next = seen then seen else closeBoolRelationAux step fuel next

/-- Directed Boolean closure from one source.  `card α + 1` rounds are more
than enough for the monotone saturation to reach a fixed point. -/
def closeBoolRelation {α : Type u} [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (source : α) : Finset α :=
  closeBoolRelationAux step (Fintype.card α + 1) {source}

/-- Executable membership in the directed finite closure. -/
def boolRelationReachable {α : Type u} [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (source target : α) : Bool :=
  decide (target ∈ closeBoolRelation step source)

theorem subset_boolRelationExpansion {α : Type u}
    [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (seen : Finset α) :
    seen ⊆ boolRelationExpansion step seen := by
  intro vertex hvertex
  exact Finset.mem_union_left _ hvertex

theorem boolRelationExpansion_card_lt_of_ne {α : Type u}
    [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (seen : Finset α)
    (hne : boolRelationExpansion step seen ≠ seen) :
    seen.card < (boolRelationExpansion step seen).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  exact ⟨subset_boolRelationExpansion step seen, fun heq => hne heq.symm⟩

theorem mem_closeBoolRelationAux_of_mem {α : Type u}
    [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (fuel : Nat) (seen : Finset α)
    {vertex : α} (hvertex : vertex ∈ seen) :
    vertex ∈ closeBoolRelationAux step fuel seen := by
  induction fuel generalizing seen with
  | zero => simpa [closeBoolRelationAux] using hvertex
  | succ fuel ih =>
      simp only [closeBoolRelationAux]
      let next := boolRelationExpansion step seen
      have hnext : vertex ∈ next :=
        subset_boolRelationExpansion step seen hvertex
      by_cases hfixed : next = seen
      · simpa [next, hfixed] using hvertex
      · simp only [next, hfixed, if_false]
        exact ih next hnext

theorem closeBoolRelationAux_lift {α : Type u}
    [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (fuel : Nat) (seen : Finset α)
    (P : α → Prop)
    (hseen : ∀ vertex, vertex ∈ seen → P vertex)
    (hstep : ∀ current target,
      P current → step current target = true → P target) :
    ∀ vertex, vertex ∈ closeBoolRelationAux step fuel seen → P vertex := by
  induction fuel generalizing seen with
  | zero =>
      intro vertex hvertex
      exact hseen vertex (by simpa [closeBoolRelationAux] using hvertex)
  | succ fuel ih =>
      intro vertex hvertex
      simp only [closeBoolRelationAux] at hvertex
      let next := boolRelationExpansion step seen
      have hnext : ∀ target, target ∈ next → P target := by
        intro target htarget
        rcases Finset.mem_union.mp htarget with htarget | htarget
        · exact hseen target htarget
        · rw [Finset.mem_filter] at htarget
          rcases htarget.2 with ⟨current, hcurrent, hcurrentTarget⟩
          exact hstep current target (hseen current hcurrent) hcurrentTarget
      by_cases hfixed : next = seen
      · simp only [next, hfixed, if_true] at hvertex
        exact hseen vertex hvertex
      · simp only [next, hfixed, if_false] at hvertex
        exact ih next hnext vertex hvertex

/-- Fuel beyond the number of still-unseen vertices forces saturation. -/
theorem closeBoolRelationAux_fixed {α : Type u}
    [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (fuel : Nat) (seen : Finset α)
    (hfuel : Fintype.card α - seen.card < fuel) :
    boolRelationExpansion step (closeBoolRelationAux step fuel seen) =
      closeBoolRelationAux step fuel seen := by
  induction fuel generalizing seen with
  | zero => omega
  | succ fuel ih =>
      simp only [closeBoolRelationAux]
      let next := boolRelationExpansion step seen
      by_cases hfixed : next = seen
      · simp [next, hfixed]
      · have hcard : seen.card < next.card :=
          boolRelationExpansion_card_lt_of_ne step seen hfixed
        have hnextCard : next.card ≤ Fintype.card α := by
          simpa using Finset.card_le_card (Finset.subset_univ next)
        have hnextFuel : Fintype.card α - next.card < fuel := by
          omega
        simp only [next, hfixed, if_false]
        exact ih next hnextFuel

theorem closeBoolRelation_fixed {α : Type u}
    [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (source : α) :
    boolRelationExpansion step (closeBoolRelation step source) =
      closeBoolRelation step source := by
  apply closeBoolRelationAux_fixed
  simp only [Finset.card_singleton]
  omega

theorem source_mem_closeBoolRelation {α : Type u}
    [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (source : α) :
    source ∈ closeBoolRelation step source := by
  exact mem_closeBoolRelationAux_of_mem step _ _ (Finset.mem_singleton_self source)

theorem closeBoolRelation_sound {α : Type u}
    [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (source target : α)
    (htarget : target ∈ closeBoolRelation step source) :
    Relation.ReflTransGen (fun left right => step left right = true)
      source target := by
  exact closeBoolRelationAux_lift step _ {source}
    (fun vertex =>
      Relation.ReflTransGen (fun left right => step left right = true)
        source vertex)
    (by
      intro vertex hvertex
      rw [Finset.mem_singleton] at hvertex
      subst vertex
      exact Relation.ReflTransGen.refl)
    (by
      intro current next hcurrent hstep
      exact Relation.ReflTransGen.tail hcurrent hstep)
    target htarget

theorem mem_closeBoolRelation_of_reflTransGen {α : Type u}
    [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (source target : α)
    (hreach : Relation.ReflTransGen
      (fun left right => step left right = true) source target) :
    target ∈ closeBoolRelation step source := by
  let closure := closeBoolRelation step source
  have hfixed : boolRelationExpansion step closure = closure :=
    closeBoolRelation_fixed step source
  induction hreach with
  | refl => exact source_mem_closeBoolRelation step source
  | tail hprefix hstep ih =>
      change _ ∈ closure
      rw [← hfixed]
      apply Finset.mem_union_right
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, _, (by simpa [closure] using ih), hstep⟩

/-- The executable directed closure is exactly reflexive-transitive closure of
the Boolean step relation. -/
@[simp]
theorem boolRelationReachable_eq_true_iff {α : Type u}
    [Fintype α] [DecidableEq α]
    (step : α → α → Bool) (source target : α) :
    boolRelationReachable step source target = true ↔
      Relation.ReflTransGen (fun left right => step left right = true)
        source target := by
  rw [boolRelationReachable, decide_eq_true_eq]
  exact ⟨closeBoolRelation_sound step source target,
    mem_closeBoolRelation_of_reflTransGen step source target⟩

end GoertzelV24FiniteBoolRelationClosure

end Mettapedia.GraphTheory.FourColor
