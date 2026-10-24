import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Card

/-!
# Foundational meaning: causal chains and grounding

K. R. Thórisson and G. Talevi, *A theory of foundational meaning generation in
autonomous systems, natural and artificial*, AGI 2024, LNAI 14951, 188–198.

An agent's knowledge contains causal models. Each describes how one
description of a situation leads to another, and carries its reliability as
explicit metaknowledge. Applying models in sequence, each to the output of the
previous one, forms a causal chain. Knowledge about a situation is grounded
when an unbroken chain connects the data perceived now to a top-level goal; a
chain is broken when one of its models falls below a threshold, and the more
reliable its weakest model, the stronger the grounding.

Here descriptions are the nodes of a knowledge graph and models are its
reliability-weighted edges. Reliabilities live in any linear order with a top.

* `le_strength_iff`: a chain meets a threshold exactly when each of its models
  does; the strength of a chain is the reliability of its weakest model.
* `strength_append`, `GroundedAt.trans`: grounding composes through an
  intermediate description, at the weaker of the two strengths.
* `GroundedAt.mono_knowledge`: learning further models never breaks grounding.
* `GroundedWithin`, `groundedAt_iff_exists_within`: meaning is generated in the
  now, so only chains that fit its time budget count; grounding is the union
  of grounding within every budget. With finitely many descriptions, a budget
  of their number suffices (`GroundedAt.within_card`).

**Controls.** In a three-model chain one weak model breaks grounding although
the other two are perfect (`Controls.weak_middle_breaks`); learning a direct
model restores it (`Controls.learning_restores`); a two-model chain is not
grounded within a one-step now (`Controls.short_now_misses`).

The theory concerns agents in the physical world. Reading formal derivations
as causal models of an agent's knowledge is an extension; see
`FoundationalMeaning.ReflectionByEvidence`.
-/

set_option autoImplicit false

namespace Mettapedia.FoundationalMeaning

universe uNode uReliability

variable {Node : Type uNode} {R : Type uReliability}

/-- A causal model: from one description of a situation to the description it
predicts, with its reliability as explicit metaknowledge. -/
structure CausalModel (Node : Type uNode) (R : Type uReliability) where
  source : Node
  target : Node
  reliability : R

/-- A causal chain from `start` to `finish` in the given knowledge: the input of
each model is the output of the previous one. -/
inductive Chain (knowledge : Set (CausalModel Node R)) :
    Node → Node → List (CausalModel Node R) → Prop
  | nil (node : Node) : Chain knowledge node node []
  | cons {model : CausalModel Node R} {finish : Node} {rest : List (CausalModel Node R)} :
      model ∈ knowledge → Chain knowledge model.target finish rest →
        Chain knowledge model.source finish (model :: rest)

namespace Chain

variable {knowledge knowledge' : Set (CausalModel Node R)}

/-- Chains concatenate at a shared description. -/
theorem append {start middle finish : Node} {first second : List (CausalModel Node R)}
    (before : Chain knowledge start middle first) (after : Chain knowledge middle finish second) :
    Chain knowledge start finish (first ++ second) := by
  induction before with
  | nil => exact after
  | cons member _ ih => exact .cons member (ih after)

/-- A chain uses only models of the knowledge it was formed in. -/
theorem mem_knowledge {start finish : Node} {chain : List (CausalModel Node R)}
    (formed : Chain knowledge start finish chain) {model : CausalModel Node R}
    (inChain : model ∈ chain) : model ∈ knowledge := by
  induction formed with
  | nil => simp at inChain
  | cons member _ ih =>
      rcases List.mem_cons.mp inChain with rfl | later
      · exact member
      · exact ih later

theorem nil_iff {start finish : Node} :
    Chain knowledge start finish [] ↔ start = finish := by
  constructor
  · intro formed
    cases formed
    rfl
  · rintro rfl
    exact .nil _

theorem cons_iff {start finish : Node} {model : CausalModel Node R}
    {rest : List (CausalModel Node R)} :
    Chain knowledge start finish (model :: rest) ↔
      model ∈ knowledge ∧ model.source = start ∧ Chain knowledge model.target finish rest := by
  constructor
  · intro formed
    cases formed with
    | cons member later => exact ⟨member, rfl, later⟩
  · rintro ⟨member, rfl, later⟩
    exact .cons member later

/-- A chain formed in some knowledge is formed in any larger knowledge. -/
theorem mono {start finish : Node} {chain : List (CausalModel Node R)}
    (larger : knowledge ⊆ knowledge') (formed : Chain knowledge start finish chain) :
    Chain knowledge' start finish chain := by
  induction formed with
  | nil node => exact .nil node
  | cons member _ ih => exact .cons (larger member) ih

/-- From any model of a chain, the rest of the chain is a chain from its source. -/
theorem suffix_from {start finish : Node} {chain : List (CausalModel Node R)}
    (formed : Chain knowledge start finish chain) {model : CausalModel Node R}
    (inChain : model ∈ chain) :
    ∃ suffix, Chain knowledge model.source finish suffix ∧ suffix.length ≤ chain.length ∧
      ∀ other ∈ suffix, other ∈ chain := by
  induction formed with
  | nil => simp at inChain
  | cons member later ih =>
      rename_i head _ rest
      rcases List.mem_cons.mp inChain with rfl | inRest
      · exact ⟨_, .cons member later, le_rfl, fun _ inSuffix => inSuffix⟩
      · obtain ⟨suffix, formed', short, sub⟩ := ih inRest
        exact ⟨suffix, formed', by simp only [List.length_cons]; omega,
          fun other inSuffix => List.mem_cons_of_mem _ (sub other inSuffix)⟩

/-- A chain that passes a description twice can skip the loop between. -/
theorem shorten {start finish : Node} {chain : List (CausalModel Node R)}
    (formed : Chain knowledge start finish chain)
    (repeated : ¬ (chain.map CausalModel.source).Nodup) :
    ∃ shorter, Chain knowledge start finish shorter ∧ shorter.length < chain.length ∧
      ∀ other ∈ shorter, other ∈ chain := by
  induction formed with
  | nil => simp at repeated
  | cons member later ih =>
      rename_i head _ rest
      rw [List.map_cons, List.nodup_cons, not_and_or, not_not] at repeated
      rcases repeated with again | restRepeated
      · obtain ⟨other, inRest, same⟩ := List.mem_map.mp again
        obtain ⟨suffix, formed', short, sub⟩ := later.suffix_from inRest
        rw [same] at formed'
        exact ⟨suffix, formed', by simp only [List.length_cons]; omega,
          fun model inSuffix => List.mem_cons_of_mem _ (sub model inSuffix)⟩
      · obtain ⟨shorter, formed', short, sub⟩ := ih restRepeated
        refine ⟨head :: shorter, .cons member formed', by simp only [List.length_cons]; omega, ?_⟩
        intro model inShorter
        rcases List.mem_cons.mp inShorter with rfl | inRest
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (sub model inRest)

end Chain

variable [LinearOrder R] [OrderTop R]

/-- The strength of a chain: the reliability of its weakest model. -/
def strength (chain : List (CausalModel Node R)) : R :=
  chain.foldr (fun model rest => min model.reliability rest) ⊤

@[simp] theorem strength_nil : strength ([] : List (CausalModel Node R)) = ⊤ := rfl

@[simp] theorem strength_cons (model : CausalModel Node R) (rest : List (CausalModel Node R)) :
    strength (model :: rest) = min model.reliability (strength rest) := rfl

/-- **The weakest link.** A chain meets a threshold exactly when every model in
it does. -/
theorem le_strength_iff (threshold : R) (chain : List (CausalModel Node R)) :
    threshold ≤ strength chain ↔ ∀ model ∈ chain, threshold ≤ model.reliability := by
  induction chain with
  | nil => simp
  | cons model rest ih => simp [ih]

/-- Concatenated chains are as strong as the weaker of the two. -/
theorem strength_append (first second : List (CausalModel Node R)) :
    strength (first ++ second) = min (strength first) (strength second) := by
  induction first with
  | nil => simp
  | cons model rest ih => simp [ih, min_assoc]

/-- Grounding at a threshold: an unbroken chain from `start` to `finish` whose
weakest model meets the threshold. -/
def GroundedAt (knowledge : Set (CausalModel Node R)) (threshold : R) (start finish : Node) :
    Prop :=
  ∃ chain, Chain knowledge start finish chain ∧ threshold ≤ strength chain

namespace GroundedAt

variable {knowledge knowledge' : Set (CausalModel Node R)} {threshold lower : R}

/-- Grounding composes through an intermediate description. -/
theorem trans {start middle finish : Node} (before : GroundedAt knowledge threshold start middle)
    (after : GroundedAt knowledge threshold middle finish) :
    GroundedAt knowledge threshold start finish := by
  obtain ⟨first, firstChain, firstStrong⟩ := before
  obtain ⟨second, secondChain, secondStrong⟩ := after
  exact ⟨first ++ second, firstChain.append secondChain,
    (strength_append first second).symm ▸ le_min firstStrong secondStrong⟩

/-- Learning never breaks grounding. -/
theorem mono_knowledge {start finish : Node} (larger : knowledge ⊆ knowledge')
    (grounded : GroundedAt knowledge threshold start finish) :
    GroundedAt knowledge' threshold start finish := by
  obtain ⟨chain, formed, strong⟩ := grounded
  exact ⟨chain, formed.mono larger, strong⟩

/-- Grounding at a threshold is grounding at every lower threshold. -/
theorem mono_threshold {start finish : Node} (le : lower ≤ threshold)
    (grounded : GroundedAt knowledge threshold start finish) :
    GroundedAt knowledge lower start finish := by
  obtain ⟨chain, formed, strong⟩ := grounded
  exact ⟨chain, formed, le.trans strong⟩

end GroundedAt

/-- Grounding within the now: a chain of at most `budget` models. -/
def GroundedWithin (knowledge : Set (CausalModel Node R)) (threshold : R) (budget : ℕ)
    (start finish : Node) : Prop :=
  ∃ chain, Chain knowledge start finish chain ∧ chain.length ≤ budget ∧
    threshold ≤ strength chain

/-- Grounding is grounding within some budget of time. -/
theorem groundedAt_iff_exists_within (knowledge : Set (CausalModel Node R)) (threshold : R)
    (start finish : Node) :
    GroundedAt knowledge threshold start finish ↔
      ∃ budget, GroundedWithin knowledge threshold budget start finish := by
  constructor
  · rintro ⟨chain, formed, strong⟩
    exact ⟨chain.length, chain, formed, le_rfl, strong⟩
  · rintro ⟨_, chain, formed, _, strong⟩
    exact ⟨chain, formed, strong⟩

/-- **With finitely many descriptions, the now needs no budget beyond their
number**: a grounded description is grounded by a chain visiting each
description at most once. -/
theorem GroundedAt.within_card [Fintype Node] {knowledge : Set (CausalModel Node R)}
    {threshold : R} {start finish : Node} (grounded : GroundedAt knowledge threshold start finish) :
    GroundedWithin knowledge threshold (Fintype.card Node) start finish := by
  obtain ⟨chain, formed, strong⟩ := grounded
  induction h : chain.length using Nat.strong_induction_on generalizing chain with
  | _ length ih =>
    subst h
    by_cases distinct : (chain.map CausalModel.source).Nodup
    · exact ⟨chain, formed, by simpa using distinct.length_le_card, strong⟩
    · obtain ⟨shorter, formed', short, sub⟩ := formed.shorten distinct
      refine ih shorter.length short shorter formed' ?_ rfl
      exact (le_strength_iff _ _).mpr fun model inShorter =>
        (le_strength_iff _ _).mp strong model (sub model inShorter)

/-! ## Controls -/

namespace Controls

/-- Perception, prediction, an active goal and a top-level goal. -/
inductive Stage where
  | perception
  | prediction
  | activeGoal
  | topGoal
  deriving DecidableEq

/-- Reliabilities in tenths: `Fin 11` runs from `0` to `10`. -/
abbrev Tenths := Fin 11

def perceive : CausalModel Stage Tenths := ⟨.perception, .prediction, 10⟩
def predictGoal : CausalModel Stage Tenths := ⟨.prediction, .activeGoal, 3⟩
def serveTop : CausalModel Stage Tenths := ⟨.activeGoal, .topGoal, 10⟩
def directGoal : CausalModel Stage Tenths := ⟨.prediction, .activeGoal, 8⟩

/-- Knowledge with a weak middle model. -/
def weakKnowledge : Set (CausalModel Stage Tenths) := {perceive, predictGoal, serveTop}

/-- The same knowledge after learning a more reliable model of the middle step. -/
def learnedKnowledge : Set (CausalModel Stage Tenths) := insert directGoal weakKnowledge

theorem weakKnowledge_chain :
    Chain weakKnowledge .perception .topGoal [perceive, predictGoal, serveTop] := by
  simp [Chain.cons_iff, Chain.nil_iff, weakKnowledge, perceive, predictGoal, serveTop]

/-- Every chain through `weakKnowledge` from perception or prediction to the top
goal uses the weak middle model. -/
theorem weak_chain_uses_middle {start finish : Stage} {chain : List (CausalModel Stage Tenths)}
    (formed : Chain weakKnowledge start finish chain) (top : finish = .topGoal)
    (early : start = .perception ∨ start = .prediction) : predictGoal ∈ chain := by
  induction chain generalizing start with
  | nil =>
      rw [Chain.nil_iff] at formed
      subst formed top
      rcases early with early | early <;> cases early
  | cons model rest ih =>
      obtain ⟨member, source, later⟩ := Chain.cons_iff.mp formed
      simp only [weakKnowledge, Set.mem_insert_iff, Set.mem_singleton_iff] at member
      rcases member with rfl | rfl | rfl
      · exact List.mem_cons_of_mem _ (ih later (Or.inr rfl))
      · exact List.mem_cons_self ..
      · subst source
        rcases early with early | early <;> cases early

/-- **One weak model breaks grounding**, although the other two are perfect. -/
theorem weak_middle_breaks : ¬ GroundedAt weakKnowledge (5 : Tenths) .perception .topGoal := by
  rintro ⟨chain, formed, strong⟩
  have weak := (le_strength_iff _ chain).mp strong predictGoal
    (weak_chain_uses_middle formed rfl (Or.inl rfl))
  exact absurd weak (by decide)

/-- The weak chain is grounded at its weakest reliability. -/
theorem weak_grounded_at_three : GroundedAt weakKnowledge (3 : Tenths) .perception .topGoal :=
  ⟨_, weakKnowledge_chain, by decide⟩

/-- **Learning restores grounding**: a more reliable model of the middle step. -/
theorem learning_restores : GroundedAt learnedKnowledge (5 : Tenths) .perception .topGoal := by
  refine ⟨[perceive, directGoal, serveTop], ?_, by decide⟩
  simp [Chain.cons_iff, Chain.nil_iff, learnedKnowledge, weakKnowledge, perceive, directGoal,
    serveTop]

/-- A two-model chain does not fit a one-step now. -/
theorem short_now_misses :
    ¬ GroundedWithin ({perceive, directGoal} : Set (CausalModel Stage Tenths)) (5 : Tenths) 1
      .perception .activeGoal := by
  rintro ⟨chain, formed, short, _⟩
  match chain, formed, short with
  | [], formed, _ => cases Chain.nil_iff.mp formed
  | [model], formed, _ =>
      obtain ⟨member, source, later⟩ := Chain.cons_iff.mp formed
      have target := Chain.nil_iff.mp later
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
      rcases member with rfl | rfl
      · cases target
      · cases source

theorem two_step_now_suffices :
    GroundedWithin ({perceive, directGoal} : Set (CausalModel Stage Tenths)) (5 : Tenths) 2
      .perception .activeGoal := by
  refine ⟨[perceive, directGoal], ?_, by decide, by decide⟩
  simp [Chain.cons_iff, Chain.nil_iff, perceive, directGoal]

end Controls

end Mettapedia.FoundationalMeaning
