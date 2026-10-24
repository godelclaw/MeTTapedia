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

A shared prefix is not by itself evidence of a cache hit. For providers with
explicit cache entries, `ExplicitPromptCache.lean` additionally models writes,
expiry and the finite lookback window. The native full-context renderer puts
completed history before current project facts; its append/revision property
is `ExplicitPromptCache.history_before_facts_keeps_hit_after_append`.
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

/-! ## History windows

`singnet/Omega` pull request #341 (head `5455049`, open) adds a flag that moves
the conversation history ahead of the per-cycle skill results, making the
layout stable-first (`stable_part_is_a_prefix`). The history section is the
tail of the history file (`read_file_tail` with `maxHistory`): a sliding window
of the newest `N` characters. While the history fits, it only grows by appending, and two
consecutive prompts share the whole history (`appended_history_shared`). Once
it exceeds `N`, every append moves the window's start, and consecutive prompts
can share nothing after the head (`sliding_window_shares_nothing`). Cutting the
history at a multiple of a block size `B` instead keeps the window's start
fixed until the history grows past the next block boundary, and the history is
shared in between (`block_window_shared`). -/

/-- The newest `N` characters of the history. -/
def window (N : Nat) (history : List α) : List α := history.drop (history.length - N)

/-- While the history fits in the window, an append keeps the old history as a
prefix of the new one. -/
theorem appended_history_shared (N : Nat) (history added : List α)
    (fits : history.length + added.length ≤ N) :
    window N history <+: window N (history ++ added) := by
  have h1 : history.length - N = 0 := by omega
  have h2 : (history ++ added).length - N = 0 := by simp; omega
  simp only [window, h1, h2, List.drop_zero]
  exact List.prefix_append history added

/-- Once the history exceeds the window, one appended character moves its start:
the two windows share no prefix. -/
theorem sliding_window_shares_nothing :
    window 3 [1, 2, 3] = [1, 2, 3] ∧ window 3 [1, 2, 3, 4] = [2, 3, 4] ∧
      ∀ common : List Nat, common <+: window 3 [1, 2, 3] →
        common <+: window 3 [1, 2, 3, 4] → common = [] := by
  refine ⟨rfl, rfl, ?_⟩
  intro common inFirst inSecond
  cases common with
  | nil => rfl
  | cons head tail =>
      have one := (List.cons_prefix_cons.mp inFirst).1
      have two := (List.cons_prefix_cons.mp inSecond).1
      omega

/-- Drop a multiple of `B` characters: the smallest one leaving at most `N`. -/
def blockCut (B N length : Nat) : Nat :=
  if length ≤ N then 0 else B * ((length - N + B - 1) / B)

def blockWindow (B N : Nat) (history : List α) : List α :=
  history.drop (blockCut B N history.length)

/-- If an append does not cross a block boundary, the old window is a prefix of
the new one. -/
theorem block_window_shared (B N : Nat) (history added : List α)
    (same : blockCut B N history.length = blockCut B N (history ++ added).length)
    (within : blockCut B N history.length ≤ history.length) :
    blockWindow B N history <+: blockWindow B N (history ++ added) := by
  unfold blockWindow
  rw [← same, List.drop_append_of_le_length within]
  exact List.prefix_append _ _

/-- Window 3, block 2: from four to five characters the sliding window shares
nothing, while the block-aligned window keeps its start and is shared. -/
theorem block_window_example :
    blockWindow 2 3 [1, 2, 3, 4] = [3, 4] ∧ blockWindow 2 3 [1, 2, 3, 4, 5] = [3, 4, 5] ∧
      blockWindow 2 3 [1, 2, 3, 4] <+: blockWindow 2 3 [1, 2, 3, 4, 5] ∧
      window 3 [1, 2, 3, 4] = [2, 3, 4] ∧ window 3 [1, 2, 3, 4, 5] = [3, 4, 5] := by
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  exact ⟨[5], rfl⟩

end PettaClaw.PromptCacheLayout

#print axioms PettaClaw.PromptCacheLayout.stable_part_is_a_prefix
#print axioms PettaClaw.PromptCacheLayout.agreeing_turns_share_the_stable_part
#print axioms PettaClaw.PromptCacheLayout.changing_text_first_can_share_nothing
#print axioms PettaClaw.PromptCacheLayout.deployed_layout_is_stable_first
#print axioms PettaClaw.PromptCacheLayout.deployed_turns_share_everything_before_the_last_boundary
#print axioms PettaClaw.PromptCacheLayout.appended_history_shared
#print axioms PettaClaw.PromptCacheLayout.sliding_window_shares_nothing
#print axioms PettaClaw.PromptCacheLayout.block_window_shared
#print axioms PettaClaw.PromptCacheLayout.block_window_example
