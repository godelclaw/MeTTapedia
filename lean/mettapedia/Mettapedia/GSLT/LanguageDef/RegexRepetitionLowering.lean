import Mettapedia.GSLT.LanguageDef.RegexSelectionLowering
import Mettapedia.Computability.RegularLanguages.Repetition

/-!+# Counted repetition as source elaboration

The result uses the existing selection Pattern and preserves its graph choices.
Positive unbounded counts end in a dedicated plus node, not a star appended
after an additional copy. Optional tails are nested rather than independent.
Source capture layout remains separate from the executable pattern, so a zero
count can omit all instructions without deleting a declared group identity.
-/

set_option autoImplicit false
open scoped Computability

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.RepetitionLowering

open Mettapedia.Computability.RegularLanguages

def prependCopies (body : Pattern) : Nat → Pattern → Pattern
  | 0, tail => tail
  | count + 1, tail => .seq body (prependCopies body count tail)

def options (body : Pattern) : Nat → Bool → Pattern
  | 0, _ => .epsilon
  | count + 1, greedy => .optional (.seq body (options body count greedy)) greedy

def exact (body : Pattern) (count : Nat) : Pattern := prependCopies body count .epsilon

def atLeast (body : Pattern) : Nat → Bool → Pattern
  | 0, greedy => .star body greedy
  | count + 1, greedy => prependCopies body count (.plus body greedy)

/-- The source boundary supplies the nonnegative difference after checking
that the upper bound is not below the lower bound. -/
def bounded (body : Pattern) (lower extra : Nat) (greedy : Bool) : Pattern :=
  prependCopies body lower (options body extra greedy)

@[simp] theorem atLeast_zero (body : Pattern) (greedy : Bool) :
    atLeast body 0 greedy = .star body greedy := rfl

@[simp] theorem atLeast_one (body : Pattern) (greedy : Bool) :
    atLeast body 1 greedy = .plus body greedy := rfl

theorem atLeast_succ (body : Pattern) (count : Nat) (greedy : Bool) :
    atLeast body (count + 1) greedy = prependCopies body count (.plus body greedy) := rfl

theorem prefix_exact (body : Pattern) (count : Nat) :
    exact body count = repeatExact body count := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [exact, prependCopies, repeatExact] using congrArg (Pattern.seq body) ih

theorem prefix_groups (body tail : Pattern) (count : Nat) :
    captureGroups (prependCopies body count tail) =
      (List.replicate count (captureGroups body)).flatten ++ captureGroups tail := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCopies, captureGroups, ih, List.replicate_succ, List.append_assoc]

theorem options_groups (body : Pattern) (count : Nat) (greedy : Bool) :
    captureGroups (options body count greedy) =
      (List.replicate count (captureGroups body)).flatten := by
  induction count with
  | zero => rfl
  | succ count ih => simp [options, captureGroups, ih, List.replicate_succ]

theorem prefix_no_new_group (body tail : Pattern) (count group : Nat)
    (member : group ∈ captureGroups (prependCopies body count tail)) :
    group ∈ captureGroups body ∨ group ∈ captureGroups tail := by
  induction count with
  | zero => exact Or.inr member
  | succ count ih =>
      simp only [prependCopies, captureGroups, List.mem_append] at member
      rcases member with member | member
      · exact Or.inl member
      · exact ih member

theorem options_no_new_group (body : Pattern) (count group : Nat) (greedy : Bool)
    (member : group ∈ captureGroups (options body count greedy)) : group ∈ captureGroups body := by
  induction count with
  | zero => cases member
  | succ count ih =>
      simp only [options, captureGroups, List.mem_append] at member
      exact member.elim id ih

structure Result where
  pattern : Pattern
  declaredGroups : List Nat
  deriving DecidableEq, Repr

def exactResult (body : Pattern) (count : Nat) : Result := ⟨exact body count, captureGroups body⟩
def atLeastResult (body : Pattern) (count : Nat) (greedy : Bool) : Result :=
  ⟨atLeast body count greedy, captureGroups body⟩
def boundedResult (body : Pattern) (lower extra : Nat) (greedy : Bool) : Result :=
  ⟨bounded body lower extra greedy, captureGroups body⟩

theorem bounded_no_new_group (body : Pattern) (lower extra group : Nat) (greedy : Bool)
    (member : group ∈ captureGroups (bounded body lower extra greedy)) : group ∈ captureGroups body := by
  exact (prefix_no_new_group body (options body extra greedy) lower group member).elim id
    (options_no_new_group body extra group greedy)

theorem atLeast_no_new_group (body : Pattern) (count group : Nat) (greedy : Bool)
    (member : group ∈ captureGroups (atLeast body count greedy)) : group ∈ captureGroups body := by
  cases count with
  | zero => exact member
  | succ count => exact (prefix_no_new_group body (.plus body greedy) count group member).elim id id

theorem language_prefix (body tail : Pattern) (count : Nat) (L K : Language Nat)
    (bodyMeaning : language? body = some L) (tailMeaning : language? tail = some K) :
    language? (prependCopies body count tail) = some (L ^ count * K) := by
  induction count with
  | zero => simpa [prependCopies] using tailMeaning
  | succ count ih => simp [prependCopies, language?, bodyMeaning, ih, pow_succ', mul_assoc]

theorem language_options (body : Pattern) (count : Nat) (greedy : Bool) (regex : Regex Nat)
    (bodyMeaning : language? body = some (language regex)) :
    language? (options body count greedy) = some (language (atMostRepeat regex count)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [options, language?, bodyMeaning, ih, atMostRepeat, sup_comm]

theorem language_exact (body : Pattern) (count : Nat) (regex : Regex Nat)
    (bodyMeaning : language? body = some (language regex)) :
    language? (exact body count) = some (language regex ^ count) := by
  simpa [exact] using language_prefix body .epsilon count (language regex) 1 bodyMeaning rfl

theorem language_atLeast (body : Pattern) (minimum : Nat) (greedy : Bool) (regex : Regex Nat)
    (bodyMeaning : language? body = some (language regex)) :
    language? (atLeast body minimum greedy) = some (language regex ^ minimum * (language regex)∗) := by
  cases minimum with
  | zero => simp [atLeast, language?, bodyMeaning]
  | succ count =>
      have plusMeaning : language? (.plus body greedy) = some (language regex * (language regex)∗) := by
        simp [language?, bodyMeaning]
      simpa [atLeast, pow_succ, mul_assoc] using
        language_prefix body (.plus body greedy) count (language regex)
          (language regex * (language regex)∗) bodyMeaning plusMeaning

theorem language_bounded (body : Pattern) (lower extra : Nat) (greedy : Bool) (regex : Regex Nat)
    (bodyMeaning : language? body = some (language regex)) :
    language? (bounded body lower extra greedy) = some (language (boundedRepeat regex lower (lower + extra))) := by
  simpa [bounded, boundedRepeat, Nat.le_add_right, Nat.add_sub_cancel_left] using
    language_prefix body (options body extra greedy) lower (language regex)
      (language (atMostRepeat regex extra)) bodyMeaning (language_options body extra greedy regex bodyMeaning)

theorem bounded_factor_counts (body : Pattern) (lower extra : Nat) (greedy : Bool) (regex : Regex Nat)
    (bodyMeaning : language? body = some (language regex)) (word : List Nat) :
    language? (bounded body lower extra greedy) = some (language (boundedRepeat regex lower (lower + extra))) ∧
      (word ∈ language (boundedRepeat regex lower (lower + extra)) ↔
        ∃ count, lower ≤ count ∧ count ≤ lower + extra ∧ word ∈ language regex ^ count) :=
  ⟨language_bounded body lower extra greedy regex bodyMeaning, mem_language_boundedRepeat regex lower (lower + extra) word⟩

namespace Controls

theorem nullable_one_or_more_is_dedicated_plus :
    compile (atLeast (.capture 1 (.alt (.literal 97) .epsilon)) 1 true) =
      compile (.plus (.capture 1 (.alt (.literal 97) .epsilon)) true) := rfl

theorem bounded_is_nested_options :
    bounded (.capture 2 (.literal 97)) 1 2 false =
      .seq (.capture 2 (.literal 97))
        (.optional (.seq (.capture 2 (.literal 97))
          (.optional (.seq (.capture 2 (.literal 97)) .epsilon) false)) false) := rfl

theorem zero_count_keeps_declared_layout :
    exactResult (.capture 3 (.literal 97)) 0 = ⟨.epsilon, [3]⟩ := rfl

theorem positive_count_is_not_copy_then_star :
    compile (atLeast (.capture 1 .epsilon) 1 true) ≠
      compile (.seq (.capture 1 .epsilon) (.star (.capture 1 .epsilon) true)) := by decide

end Controls
end Mettapedia.GSLT.LanguageDef.RegexSelection.RepetitionLowering
