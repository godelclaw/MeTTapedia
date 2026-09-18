import Mettapedia.Combinatorics.Reconfiguration.Fibration
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

/-!
# Completability of reconfiguration systems

Full connectivity of a reconfiguration system is often stronger than what a
colouring argument consumes.  What is consumed is *completability* towards a
target set: from every state, some target state is reachable.

`WeaklyCompletable step target` is the loaded form in which the route states
weak completability: from every state a target is reachable, *provided* some
target state exists.  For Kempe dynamics on a tangle with boundary words `W`,
the target is the set of colourings whose word lies in `W`.

The file records the basic closure properties, the transport of
completability along step lifting (the one-sided mechanism behind square
transport), and the two-sided cover skeleton: if every state lies in the image
of one of two sides whose moves embed, and each side is completable within
itself, the whole system is completable.
-/

namespace Mettapedia.Combinatorics.Reconfiguration

open Relation

universe u v w

section Basic

variable {α : Type u} (step : α → α → Prop) (target : Set α)

/-- From every state some target state is reachable. -/
def Completable : Prop :=
  ∀ x, ∃ y ∈ target, ReflTransGen step x y

/-- Completability, provided the target is inhabited. -/
def WeaklyCompletable : Prop :=
  target.Nonempty → Completable step target

variable {step target}

theorem Completable.weaklyCompletable (h : Completable step target) :
    WeaklyCompletable step target :=
  fun _ => h

theorem WeaklyCompletable.completable (h : WeaklyCompletable step target)
    (hne : target.Nonempty) : Completable step target :=
  h hne

/-- An inhabited system completable towards a target has an inhabited target. -/
theorem Completable.nonempty [Nonempty α] (h : Completable step target) :
    target.Nonempty := by
  obtain ⟨y, hy, _⟩ := h (Classical.arbitrary α)
  exact ⟨y, hy⟩

theorem completable_iff_weaklyCompletable_and_nonempty [Nonempty α] :
    Completable step target ↔ WeaklyCompletable step target ∧ target.Nonempty :=
  ⟨fun h => ⟨h.weaklyCompletable, h.nonempty⟩, fun h => h.1 h.2⟩

/-- Every system is completable towards the whole state space. -/
theorem completable_univ : Completable step Set.univ :=
  fun x => ⟨x, Set.mem_univ x, ReflTransGen.refl⟩

theorem Completable.mono_target {target' : Set α} (hsub : target ⊆ target')
    (h : Completable step target) : Completable step target' :=
  fun x => (h x).imp fun _ hy => ⟨hsub hy.1, hy.2⟩

theorem Completable.mono_step {step' : α → α → Prop}
    (hle : ∀ x y, step x y → step' x y) (h : Completable step target) :
    Completable step' target :=
  fun x => (h x).imp fun _ hy => ⟨hy.1, hy.2.mono hle⟩

theorem WeaklyCompletable.mono_step {step' : α → α → Prop}
    (hle : ∀ x y, step x y → step' x y) (h : WeaklyCompletable step target) :
    WeaklyCompletable step' target :=
  fun hne => (h hne).mono_step hle

/-- **Relay.**  Reaching an intermediate set from which the final target is
reachable reaches the final target. -/
theorem Completable.trans {target' : Set α} (h : Completable step target)
    (hrelay : ∀ t ∈ target, ∃ u ∈ target', ReflTransGen step t u) :
    Completable step target' := by
  intro x
  obtain ⟨t, ht, hxt⟩ := h x
  obtain ⟨u, hu, htu⟩ := hrelay t ht
  exact ⟨u, hu, hxt.trans htu⟩

/-- Connectivity gives completability towards every inhabited target. -/
theorem Connected.completable (h : Connected step) (hne : target.Nonempty) :
    Completable step target := by
  intro x
  obtain ⟨y, hy⟩ := hne
  exact ⟨y, hy, h x y⟩

/-- Connectivity gives weak completability towards every target. -/
theorem Connected.weaklyCompletable (h : Connected step) :
    WeaklyCompletable step target :=
  fun hne => h.completable hne

/-- **Fibrewise connectivity gives completability** as soon as every fibre
meets the target. -/
theorem FibresConnected.completable {β : Type v} {label : α → β}
    (h : FibresConnected step label)
    (hmeet : ∀ x, ∃ y ∈ target, label y = label x) :
    Completable step target := by
  intro x
  obtain ⟨y, hy, hlabel⟩ := hmeet x
  exact ⟨y, hy, h x y hlabel.symm⟩

end Basic

section Transport

variable {α : Type u} {β : Type v} {step : α → α → Prop}
  {stepβ : β → β → Prop} {target : Set α}

/-- **Transport along a covering map of moves.**  If `f` maps moves to moves
and every state is an image, completability of the source towards the preimage
of a target gives completability towards the target. -/
theorem Completable.of_map (f : β → α)
    (hstep : ∀ a b, stepβ a b → step (f a) (f b))
    (hcover : ∀ x, ∃ a, f a = x)
    (h : Completable stepβ (f ⁻¹' target)) : Completable step target := by
  intro x
  obtain ⟨a, rfl⟩ := hcover x
  obtain ⟨b, hb, hab⟩ := h a
  exact ⟨f b, hb, ReflTransGen.lift f (fun u v huv => hstep u v huv) hab⟩

variable {L : Type v} {R : Type w} {stepL : L → L → Prop} {stepR : R → R → Prop}

/-- A disjoint union of two completable systems is completable. -/
theorem completable_sum {targetL : Set L} {targetR : Set R}
    (hL : Completable stepL targetL) (hR : Completable stepR targetR) :
    Completable (Sum.LiftRel stepL stepR) (fun s => Sum.elim (· ∈ targetL) (· ∈ targetR) s) := by
  intro s
  cases s with
  | inl a =>
      obtain ⟨b, hb, hab⟩ := hL a
      exact ⟨Sum.inl b, hb,
        ReflTransGen.lift Sum.inl (fun _ _ h => Sum.LiftRel.inl h) hab⟩
  | inr a =>
      obtain ⟨b, hb, hab⟩ := hR a
      exact ⟨Sum.inr b, hb,
        ReflTransGen.lift Sum.inr (fun _ _ h => Sum.LiftRel.inr h) hab⟩

/-- **Two-sided cover.**  If every state lies in the image of one of two sides
whose moves embed as moves, and each side is completable towards the preimage
of the target, the whole system is completable.  Each witnessing path stays
inside the side it started in. -/
theorem completable_of_two_sides (includeL : L → α) (includeR : R → α)
    (hstepL : ∀ a b, stepL a b → step (includeL a) (includeL b))
    (hstepR : ∀ a b, stepR a b → step (includeR a) (includeR b))
    (hcover : ∀ x, (∃ a, includeL a = x) ∨ (∃ a, includeR a = x))
    (hL : Completable stepL (includeL ⁻¹' target))
    (hR : Completable stepR (includeR ⁻¹' target)) :
    Completable step target := by
  refine Completable.of_map (Sum.elim includeL includeR) ?_ ?_
    ((completable_sum hL hR).mono_target ?_)
  · intro a b hab
    cases hab with
    | inl h => exact hstepL _ _ h
    | inr h => exact hstepR _ _ h
  · intro x
    rcases hcover x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨Sum.inl a, ha⟩
    · exact ⟨Sum.inr a, ha⟩
  · intro s hs
    cases s with
    | inl a => exact hs
    | inr a => exact hs

end Transport

section Lifting

variable {Total : Type u} {Base : Type v}
  {totalStep : Total → Total → Prop} {baseStep : Base → Base → Prop}
  {proj : Total → Base} {targetUp : Set Total} {targetDown : Set Base}

/-- **Completability lifts along step lifting.**  If the projection of every
state reaches a base target, every base move lifts, and every state over a base
target reaches a total target, then the total system is completable.  No
fibre connectivity is needed: only the fibres over base targets are used, and
only for completion. -/
theorem LiftsSteps.completable (hlift : LiftsSteps totalStep baseStep proj)
    (hbase : ∀ x, ∃ b ∈ targetDown, ReflTransGen baseStep (proj x) b)
    (hfibre : ∀ x, proj x ∈ targetDown → ∃ y ∈ targetUp, ReflTransGen totalStep x y) :
    Completable totalStep targetUp := by
  intro x
  obtain ⟨b, hb, hpath⟩ := hbase x
  obtain ⟨y, hy, hxy⟩ := hlift.lift hpath
  obtain ⟨z, hz, hyz⟩ := hfibre y (hy ▸ hb)
  exact ⟨z, hz, hxy.trans hyz⟩

/-- The special case in which a state over a base target is already a total
target. -/
theorem LiftsSteps.completable_of_preimage
    (hlift : LiftsSteps totalStep baseStep proj)
    (hword : ∀ y, proj y ∈ targetDown → y ∈ targetUp)
    (hbase : Completable baseStep targetDown) :
    Completable totalStep targetUp :=
  hlift.completable (fun x => hbase (proj x))
    (fun x hx => ⟨x, hword x hx, ReflTransGen.refl⟩)

/-- The loaded form: an inhabited base target and weak completability of the
base suffice. -/
theorem LiftsSteps.completable_of_weaklyCompletable
    (hlift : LiftsSteps totalStep baseStep proj)
    (hword : ∀ y, proj y ∈ targetDown → y ∈ targetUp)
    (hne : targetDown.Nonempty)
    (hbase : WeaklyCompletable baseStep targetDown) :
    Completable totalStep targetUp :=
  hlift.completable_of_preimage hword (hbase hne)

/-- A surjective projection carries an inhabited base target to an inhabited
total target. -/
theorem nonempty_of_surjective (hsurj : Function.Surjective proj)
    (hword : ∀ y, proj y ∈ targetDown → y ∈ targetUp)
    (hne : targetDown.Nonempty) : targetUp.Nonempty := by
  obtain ⟨b, hb⟩ := hne
  obtain ⟨y, rfl⟩ := hsurj b
  exact ⟨y, hword y hb⟩

end Lifting

end Mettapedia.Combinatorics.Reconfiguration
