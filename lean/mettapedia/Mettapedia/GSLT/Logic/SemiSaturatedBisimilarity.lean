import Mettapedia.GSLT.Logic.IPOSystem

/-!
# Least labels characterize saturated bisimilarity, semi-saturated

Two agents are **saturated bisimilar** when, in every context, every reaction of one is matched by a reaction of the
other, and the results are again saturated bisimilar. That is the equivalence "no environment can tell them apart",
but it quantifies over every context at every step.

A step under a least label (an idem pushout, `ActIPO`) says exactly what the environment must contribute for a rule
to fire. Bisimilarity over least labels alone is strictly finer than the saturated one: an absorbable token is
saturated bisimilar to nothing, yet it has a least-labelled step that nothing lacks
(`SaturatedRelativeBisimilarityControls.TokenAbsorption`). The repair keeps the least labels on the challenging side
and lets the answering side react in the label's context, however it likes (**semi-saturated** bisimilarity).

- **Saturated bisimulations are semi-saturated** (`semiSaturated_of_saturated`): a least-labelled step is a reaction in
  the label's context.
- **With relative pushouts for the spans of the rules, semi-saturated bisimilarity is saturated**
  (`saturated_of_semiSaturated`): a reaction in an arbitrary context factors through a least label followed by a
  residual context; the least-labelled step is matched, and the residual context is put back, since reactions are
  closed under contexts (`Reacts.comp`).
- So the two coincide (`semiSaturated_iff_saturated`), and least-labelled bisimilarity, being finer, is contained in
  both (`saturated_of_ipoBisimilar`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.SemiSaturated

open CategoryTheory
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe v u

variable {C : Type u} [Category.{v} C] {origin : C} (rules : ReactionRule origin → Prop)

/-- **A reaction**: the agent is a rule's redex in some context, and becomes the rule's reactum in that context. -/
def Reacts {interface : C} (agent next : origin ⟶ interface) : Prop :=
  ∃ rule : ReactionRule origin, rules rule ∧ ∃ reaction : rule.codomain ⟶ interface,
    agent = rule.redex ≫ reaction ∧ next = rule.reactum ≫ reaction

variable {rules}

/-- **Reactions are closed under contexts.** -/
theorem Reacts.comp {interface outer : C} {agent next : origin ⟶ interface} (reacts : Reacts rules agent next)
    (context : interface ⟶ outer) : Reacts rules (agent ≫ context) (next ≫ context) := by
  obtain ⟨rule, member, reaction, rfl, rfl⟩ := reacts
  exact ⟨rule, member, reaction ≫ context, (Category.assoc _ _ _), (Category.assoc _ _ _)⟩

/-- **A least-labelled step is a reaction in the label's context.** -/
theorem Reacts.of_actIPO {interface next : C} {label : interface ⟶ next} {agent : origin ⟶ interface}
    {target : origin ⟶ next} (step : ActIPO rules label agent target) : Reacts rules (agent ≫ label) target := by
  obtain ⟨rule, member, reaction, square, -, rfl⟩ := step
  exact ⟨rule, member, reaction, square, rfl⟩

variable (rules)

/-- A family of relations, one at each interface. -/
abbrev Relation (C : Type u) [Category.{v} C] (origin : C) :=
  (interface : C) → (origin ⟶ interface) → (origin ⟶ interface) → Prop

/-- **A saturated bisimulation**: in every context, a reaction of either side is matched by a reaction of the other. -/
def IsSaturated (relation : Relation C origin) : Prop :=
  ∀ {interface : C} (left right : origin ⟶ interface), relation interface left right →
    ∀ {outer : C} (context : interface ⟶ outer),
      (∀ next, Reacts rules (left ≫ context) next →
        ∃ matched, Reacts rules (right ≫ context) matched ∧ relation outer next matched) ∧
      (∀ next, Reacts rules (right ≫ context) next →
        ∃ matched, Reacts rules (left ≫ context) matched ∧ relation outer matched next)

/-- **A semi-saturated bisimulation**: a least-labelled step of either side is matched by a reaction of the other in
the label's context. -/
def IsSemiSaturated (relation : Relation C origin) : Prop :=
  ∀ {interface : C} (left right : origin ⟶ interface), relation interface left right →
    (∀ {next : C} (label : interface ⟶ next) target, ActIPO rules label left target →
      ∃ matched, Reacts rules (right ≫ label) matched ∧ relation next target matched) ∧
    (∀ {next : C} (label : interface ⟶ next) target, ActIPO rules label right target →
      ∃ matched, Reacts rules (left ≫ label) matched ∧ relation next matched target)

/-- **Saturated bisimilarity.** -/
def SaturatedBisimilar {interface : C} (left right : origin ⟶ interface) : Prop :=
  ∃ relation, IsSaturated rules relation ∧ relation interface left right

/-- **Semi-saturated bisimilarity.** -/
def SemiSaturatedBisimilar {interface : C} (left right : origin ⟶ interface) : Prop :=
  ∃ relation, IsSemiSaturated rules relation ∧ relation interface left right

variable {rules}

/-- **Saturated bisimulations are semi-saturated.** -/
theorem semiSaturated_of_saturated {relation : Relation C origin} (saturated : IsSaturated rules relation) :
    IsSemiSaturated rules relation := by
  intro interface left right related
  constructor
  · intro next label target step
    exact (saturated left right related label).1 target (Reacts.of_actIPO step)
  · intro next label target step
    exact (saturated left right related label).2 target (Reacts.of_actIPO step)

/-- Relative pushouts for the spans of an agent and a rule's redex. -/
def HasRedexRPOs (rules : ReactionRule origin → Prop) : Prop :=
  ∀ (interface : C) (agent : origin ⟶ interface) (rule : ReactionRule origin),
    rules rule → HasRelativePushouts agent rule.redex

/-- The closure of a relation under contexts. -/
def InContext (relation : Relation C origin) : Relation C origin := fun outer first second =>
  ∃ (interface : C) (left right : origin ⟶ interface) (context : interface ⟶ outer),
    relation interface left right ∧ first = left ≫ context ∧ second = right ≫ context

/-- **A reaction in a context factors through a least label**: its step under the least label, and the residual
context that puts it back. -/
theorem factor_reaction (hasRPOs : HasRedexRPOs rules) {interface outer : C} {agent : origin ⟶ interface}
    {context : interface ⟶ outer} {next : origin ⟶ outer} (reacts : Reacts rules (agent ≫ context) next) :
    ∃ (apex : C) (label : interface ⟶ apex) (residual : apex ⟶ outer) (target : origin ⟶ apex),
      ActIPO rules label agent target ∧ label ≫ residual = context ∧ next = target ≫ residual := by
  obtain ⟨rule, member, reaction, square, rfl⟩ := reacts
  obtain ⟨reduced, rpo⟩ := hasRPOs _ agent rule member _ context reaction square
  refine ⟨reduced.apex, reduced.inl, reduced.down, rule.reactum ≫ reduced.inr,
    ⟨rule, member, reduced.inr, reduced.comm, isIdemPushout_of_isRelativePushout rpo, rfl⟩,
    reduced.fac_left, ?_⟩
  rw [Category.assoc, reduced.fac_right]

/-- **A semi-saturated bisimulation, closed under contexts, is saturated**, when the rules' spans have relative
pushouts. -/
theorem isSaturated_inContext (hasRPOs : HasRedexRPOs rules) {relation : Relation C origin}
    (semi : IsSemiSaturated rules relation) : IsSaturated rules (InContext relation) := by
  intro outer first second related outer' context
  obtain ⟨interface, left, right, inner, holds, rfl, rfl⟩ := related
  constructor
  · intro next reacts
    rw [Category.assoc] at reacts
    obtain ⟨apex, label, residual, target, step, factors, rfl⟩ := factor_reaction hasRPOs reacts
    obtain ⟨matched, matchedReacts, matchedRelated⟩ := (semi left right holds).1 label target step
    refine ⟨matched ≫ residual, ?_, apex, target, matched, residual, matchedRelated, rfl, rfl⟩
    have reacted := matchedReacts.comp residual
    rwa [Category.assoc, factors, ← Category.assoc] at reacted
  · intro next reacts
    rw [Category.assoc] at reacts
    obtain ⟨apex, label, residual, target, step, factors, rfl⟩ := factor_reaction hasRPOs reacts
    obtain ⟨matched, matchedReacts, matchedRelated⟩ := (semi left right holds).2 label target step
    refine ⟨matched ≫ residual, ?_, apex, matched, target, residual, matchedRelated, rfl, rfl⟩
    have reacted := matchedReacts.comp residual
    rwa [Category.assoc, factors, ← Category.assoc] at reacted

/-- **Semi-saturated bisimilarity is saturated**, when the rules' spans have relative pushouts. -/
theorem saturated_of_semiSaturated (hasRPOs : HasRedexRPOs rules) {interface : C} {left right : origin ⟶ interface}
    (bisimilar : SemiSaturatedBisimilar rules left right) : SaturatedBisimilar rules left right := by
  obtain ⟨relation, semi, related⟩ := bisimilar
  exact ⟨InContext relation, isSaturated_inContext hasRPOs semi,
    interface, left, right, 𝟙 _, related, (Category.comp_id _).symm, (Category.comp_id _).symm⟩

/-- **Least labels characterize saturated bisimilarity**, semi-saturated, when the rules' spans have relative
pushouts. -/
theorem semiSaturated_iff_saturated (hasRPOs : HasRedexRPOs rules) {interface : C} {left right : origin ⟶ interface} :
    SemiSaturatedBisimilar rules left right ↔ SaturatedBisimilar rules left right :=
  ⟨saturated_of_semiSaturated hasRPOs, fun ⟨relation, saturated, related⟩ =>
    ⟨relation, semiSaturated_of_saturated saturated, related⟩⟩

/-- **Least-labelled bisimilarity is semi-saturated**: a matching least-labelled step is a reaction in the label's
context. -/
theorem semiSaturated_of_ipoBisimilar {interface : C} {left right : origin ⟶ interface}
    (bisimilar : IPOBisimilar rules left right) : SemiSaturatedBisimilar rules left right := by
  obtain ⟨relation, bisimulation, related⟩ := bisimilar
  refine ⟨relation, ?_, related⟩
  intro interface left right holds
  obtain ⟨forward, backward⟩ := bisimulation left right holds
  constructor
  · intro next label target step
    obtain ⟨matched, matchedStep, matchedRelated⟩ := forward label target step
    exact ⟨matched, Reacts.of_actIPO matchedStep, matchedRelated⟩
  · intro next label target step
    obtain ⟨matched, matchedStep, matchedRelated⟩ := backward label target step
    exact ⟨matched, Reacts.of_actIPO matchedStep, matchedRelated⟩

/-- **Least-labelled bisimilarity is saturated**, when the rules' spans have relative pushouts. -/
theorem saturated_of_ipoBisimilar (hasRPOs : HasRedexRPOs rules) {interface : C} {left right : origin ⟶ interface}
    (bisimilar : IPOBisimilar rules left right) : SaturatedBisimilar rules left right :=
  saturated_of_semiSaturated hasRPOs (semiSaturated_of_ipoBisimilar bisimilar)

end Mettapedia.GSLT.SemiSaturated
