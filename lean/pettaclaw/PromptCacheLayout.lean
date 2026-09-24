import Mathlib

/-!
# Prompt cache layout: stable text ahead of per-turn text

A provider's prompt cache reuses a request prefix it has already seen.  An
agent's prompt mixes text that never changes (its prompt, skills, and
instructions), text that changes rarely (project state, the conversation), and
text that changes every turn (budgets, results, time, new input).

This file proves the ordering property the runtime relies on.  When the
segments are laid out least changeable first, the text at or below any level
is a prefix of the whole prompt, so two turns that agree on it share it as a
common prefix: that is the cacheable part.  One changing segment placed ahead
of stable text can make two prompts share nothing, however much stable text
follows.  The deployed layout (head, stable sources, conversation, per-turn
state, with a cache boundary after each of the first three) is an instance.
-/

namespace PettaClaw.PromptCacheLayout

/-- A piece of the prompt and how often it changes (`0`: never). -/
structure Segment (α : Type*) where
  level : Nat
  text : List α

variable {α : Type*}

/-- The text a provider receives. -/
def render (segments : List (Segment α)) : List α :=
  (segments.map Segment.text).flatten

/-- Least changeable first. -/
def StableFirst (segments : List (Segment α)) : Prop :=
  segments.Pairwise (fun a b => a.level ≤ b.level)

/-- The segments that change at most as often as `level`. -/
def upTo (level : Nat) (segments : List (Segment α)) : List (Segment α) :=
  segments.filter (fun segment => segment.level ≤ level)

theorem render_cons (segment : Segment α) (rest : List (Segment α)) :
    render (segment :: rest) = segment.text ++ render rest := by
  simp [render]

/-- In a stable-first layout, the text up to any level is a prefix. -/
theorem stable_part_is_a_prefix (level : Nat) :
    ∀ segments : List (Segment α), StableFirst segments →
      render (upTo level segments) <+: render segments
  | [], _ => by simp [render, upTo]
  | segment :: rest, ordered => by
      rw [StableFirst, List.pairwise_cons] at ordered
      obtain ⟨below, restOrdered⟩ := ordered
      by_cases kept : segment.level ≤ level
      · have tail := stable_part_is_a_prefix level rest restOrdered
        have keptList : upTo level (segment :: rest) =
            segment :: upTo level rest := by
          simp [upTo, kept]
        rw [keptList, render_cons, render_cons]
        exact (List.prefix_append_right_inj segment.text).mpr tail
      · have dropped : upTo level (segment :: rest) = [] := by
          simp only [upTo, List.filter_cons, kept, decide_false,
            Bool.false_eq_true, if_false]
          rw [List.filter_eq_nil_iff]
          intro later member
          have := below later member
          simp only [decide_eq_true_eq, not_le]
          omega
        rw [dropped]
        exact List.nil_prefix

/-- Two turns that agree on everything up to a level share that text as a
common prefix of their prompts. -/
theorem agreeing_turns_share_the_stable_part (level : Nat)
    (first second : List (Segment α))
    (firstOrdered : StableFirst first) (secondOrdered : StableFirst second)
    (same : upTo level first = upTo level second) :
    render (upTo level first) <+: render first ∧
      render (upTo level first) <+: render second := by
  refine ⟨stable_part_is_a_prefix level first firstOrdered, ?_⟩
  rw [same]
  exact stable_part_is_a_prefix level second secondOrdered

/-- Changing text ahead of stable text: the two prompts agree on all their
stable text, yet share no prefix at all, so nothing can be reused. -/
theorem changing_text_first_can_share_nothing :
    let first : List (Segment Nat) := [⟨1, [0]⟩, ⟨0, [7, 7, 7]⟩]
    let second : List (Segment Nat) := [⟨1, [1]⟩, ⟨0, [7, 7, 7]⟩]
    upTo 0 first = upTo 0 second ∧ ¬ StableFirst first ∧
      ∀ common, common <+: render first → common <+: render second →
        common = [] := by
  refine ⟨rfl, by simp [StableFirst], ?_⟩
  intro common inFirst inSecond
  cases common with
  | nil => rfl
  | cons head tail =>
      have zero := (List.cons_prefix_cons.mp inFirst).1
      have one := (List.cons_prefix_cons.mp inSecond).1
      omega

/-- The deployed layout, with its levels. -/
def deployed (head stable conversation turn : List α) : List (Segment α) :=
  [⟨0, head⟩, ⟨1, stable⟩, ⟨2, conversation⟩, ⟨3, turn⟩]

theorem deployed_layout_is_stable_first
    (head stable conversation turn : List α) :
    StableFirst (deployed head stable conversation turn) := by
  simp [StableFirst, deployed]

/-- Whatever changes per turn, two deployed prompts with the same head,
stable sources, and conversation share all the text before the last cache
boundary. -/
theorem deployed_turns_share_everything_before_the_last_boundary
    (head stable conversation turn turn' : List α) :
    head ++ stable ++ conversation <+:
        render (deployed head stable conversation turn) ∧
      head ++ stable ++ conversation <+:
        render (deployed head stable conversation turn') := by
  have shared (last : List α) :
      head ++ stable ++ conversation <+:
        render (deployed head stable conversation last) := by
    simp [deployed, render]
  exact ⟨shared turn, shared turn'⟩

end PettaClaw.PromptCacheLayout

#print axioms PettaClaw.PromptCacheLayout.stable_part_is_a_prefix
#print axioms PettaClaw.PromptCacheLayout.agreeing_turns_share_the_stable_part
#print axioms PettaClaw.PromptCacheLayout.changing_text_first_can_share_nothing
#print axioms PettaClaw.PromptCacheLayout.deployed_layout_is_stable_first
#print axioms PettaClaw.PromptCacheLayout.deployed_turns_share_everything_before_the_last_boundary
