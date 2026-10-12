import Mettapedia.OSLF.NativeTypes.Decision.Stream.Bind
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Suspended equivalence-aware structural matching

Every pattern inspection is suspended. Bag search advances physical term
positions and recursive alternatives separately, without first materializing
the complete matcher result. Primitive binding merges remain single jobs.
The exhaustive comparison preserves the original match order and duplicates.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Structural.Matching

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling

mutual

def arguments (equivalent : Pattern → Pattern → Bool)
    (patterns terms : List Pattern) : Stream Bindings := .pause fun _ =>
  match patterns, terms with
  | [], [] => .yield [] fun _ => .done
  | pattern :: patterns, term :: terms =>
      Stream.bind (patternMatches equivalent pattern term) fun headBindings =>
        Stream.filterMap (mergeBindingsWith equivalent headBindings)
          (arguments equivalent patterns terms)
  | _, _ => .done
termination_by sizeOf patterns
decreasing_by all_goals sizeOf_pattern_dec

def bag (equivalent : Pattern → Pattern → Bool) (patterns : List Pattern)
    (rest : Option String) (collectionType : CollType) (terms : List Pattern) :
    Stream Bindings := .pause fun _ =>
  match patterns with
  | [] =>
      match rest with
      | none => if terms.isEmpty then .yield [] fun _ => .done else .done
      | some name => .yield [(name, .collection collectionType terms none)] fun _ => .done
  | pattern :: patterns =>
      Stream.bind (Stream.enumerate (Stream.ofList terms)) fun (term, index) =>
        Stream.bind (patternMatches equivalent pattern term) fun headBindings =>
          Stream.filterMap (mergeBindingsWith equivalent headBindings)
            (bag equivalent patterns rest collectionType (terms.eraseIdx index))
termination_by sizeOf patterns
decreasing_by all_goals sizeOf_pattern_dec

def patternMatches (equivalent : Pattern → Pattern → Bool)
    (pattern term : Pattern) : Stream Bindings := .pause fun _ =>
  match pattern, term with
  | .fvar name, value => .yield [(name, value)] fun _ => .done
  | .bvar left, .bvar right =>
      if left == right then .yield [] fun _ => .done else .done
  | .apply leftConstructor leftArguments, .apply rightConstructor rightArguments =>
      if leftConstructor == rightConstructor && leftArguments.length == rightArguments.length then
        arguments equivalent leftArguments rightArguments
      else .done
  | .lambda _ leftBody, .lambda _ rightBody => patternMatches equivalent leftBody rightBody
  | .multiLambda leftArity _ leftBody, .multiLambda rightArity _ rightBody =>
      if leftArity == rightArity then patternMatches equivalent leftBody rightBody else .done
  | .collection leftType leftElements leftRest, .collection rightType rightElements _ =>
      if leftType == rightType then
        if leftType == .vec then
          match leftRest with
          | none => arguments equivalent leftElements rightElements
          | some name =>
              Stream.filterMap (fun bindings => mergeBindingsWith equivalent bindings
                [(name, .collection .vec (rightElements.drop leftElements.length) none)])
                (arguments equivalent leftElements (rightElements.take leftElements.length))
        else bag equivalent leftElements leftRest leftType rightElements
      else .done
  | .subst leftBody leftReplacement, .subst rightBody rightReplacement =>
      Stream.bind (patternMatches equivalent leftBody rightBody) fun bodyBindings =>
        Stream.filterMap (mergeBindingsWith equivalent bodyBindings)
          (patternMatches equivalent leftReplacement rightReplacement)
  | _, _ => .done
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

end

mutual

theorem flatten_arguments (equivalent : Pattern → Pattern → Bool) :
    (patterns terms : List Pattern) →
      (arguments equivalent patterns terms).flatten = matchArgsWith equivalent patterns terms
  | [], [] => by rw [arguments.eq_def, matchArgsWith.eq_def]; rfl
  | [], _ :: _ => by rw [arguments.eq_def, matchArgsWith.eq_def]; rfl
  | _ :: _, [] => by rw [arguments.eq_def, matchArgsWith.eq_def]; rfl
  | pattern :: patterns, term :: terms => by
      rw [arguments.eq_def, matchArgsWith.eq_def]
      change (Stream.bind _ _).flatten = _
      rw [Stream.flatten_bind, flatten_matches]
      congr 1
      funext headBindings
      rw [Stream.flatten_filterMap, flatten_arguments]
termination_by patterns _ => sizeOf patterns
decreasing_by all_goals sizeOf_pattern_dec

theorem flatten_bag (equivalent : Pattern → Pattern → Bool) :
    (patterns : List Pattern) → (rest : Option String) → (collectionType : CollType) →
      (terms : List Pattern) →
      (bag equivalent patterns rest collectionType terms).flatten =
        matchBagWith equivalent patterns rest collectionType terms
  | [], none, _, _ => by
      rw [bag.eq_def, matchBagWith.eq_def]
      change (if _ then _ else _ : Stream Bindings).flatten = _
      dsimp only
      split
      · rename_i empty
        rfl
      · rename_i nonempty
        rfl
  | [], some _, _, _ => by rw [bag.eq_def, matchBagWith.eq_def]; rfl
  | pattern :: patterns, rest, collectionType, terms => by
      rw [bag.eq_def, matchBagWith.eq_def]
      change (Stream.bind _ _).flatten = _
      rw [Stream.flatten_bind, Stream.flatten_enumerate, Stream.flatten_ofList]
      congr 1
      funext alternative
      rw [Stream.flatten_bind, flatten_matches]
      congr 1
      funext headBindings
      rw [Stream.flatten_filterMap, flatten_bag]
termination_by patterns _ _ _ => sizeOf patterns
decreasing_by all_goals sizeOf_pattern_dec

theorem flatten_matches (equivalent : Pattern → Pattern → Bool)
    (pattern term : Pattern) :
    (patternMatches equivalent pattern term).flatten = matchPatternWith equivalent pattern term := by
  cases pattern <;> cases term
  all_goals try (rw [patternMatches.eq_def, matchPatternWith.eq_def]; rfl)
  case bvar.bvar left right =>
    rw [patternMatches.eq_def, matchPatternWith.eq_def]
    change (if _ then _ else _ : Stream Bindings).flatten = _
    dsimp only
    split
    · rename_i same
      rfl
    · rename_i different
      rfl
  case apply.apply leftConstructor leftArguments rightConstructor rightArguments =>
    rw [patternMatches.eq_def, matchPatternWith.eq_def]
    change (if _ then _ else _ : Stream Bindings).flatten = _
    dsimp only
    split
    · rename_i same
      exact flatten_arguments equivalent leftArguments rightArguments
    · rename_i different
      rfl
  case lambda.lambda leftName leftBody rightName rightBody =>
    rw [patternMatches.eq_def, matchPatternWith.eq_def]
    exact flatten_matches equivalent leftBody rightBody
  case multiLambda.multiLambda leftArity leftNames leftBody rightArity rightNames rightBody =>
    rw [patternMatches.eq_def, matchPatternWith.eq_def]
    change (if _ then _ else _ : Stream Bindings).flatten = _
    dsimp only
    split
    · rename_i same
      exact flatten_matches equivalent leftBody rightBody
    · rename_i different
      rfl
  case collection.collection leftType leftElements leftRest rightType rightElements rightRest =>
    rw [patternMatches.eq_def, matchPatternWith.eq_def]
    change (if _ then _ else _ : Stream Bindings).flatten = _
    dsimp only
    split
    · rename_i same
      split
      · rename_i vector
        cases leftRest with
        | none => exact flatten_arguments equivalent leftElements rightElements
        | some name =>
            rw [Stream.flatten_filterMap, flatten_arguments]
      · rename_i nonvector
        exact flatten_bag equivalent leftElements leftRest leftType rightElements
    · rename_i different
      rfl
  case subst.subst leftBody leftReplacement rightBody rightReplacement =>
    rw [patternMatches.eq_def, matchPatternWith.eq_def]
    change (Stream.bind _ _).flatten = _
    rw [Stream.flatten_bind, flatten_matches]
    congr 1
    funext bodyBindings
    rw [Stream.flatten_filterMap, flatten_matches]
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

end

def state (equivalent : Pattern → Pattern → Bool) (pattern term : Pattern) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (patternMatches equivalent pattern term) budget

theorem exact_resume (equivalent : Pattern → Pattern → Bool)
    (pattern term : Pattern) (first more : Nat) :
    state equivalent pattern term (first + more) =
      resume more (state equivalent pattern term first) :=
  run_resume (patternMatches equivalent pattern term) first more

theorem ordered_partition (equivalent : Pattern → Pattern → Bool)
    (pattern term : Pattern) (budget : Nat) :
    (state equivalent pattern term budget).outputs ++
      (state equivalent pattern term budget).pending.flatten =
        matchPatternWith equivalent pattern term :=
  (run_partition _ _).trans (flatten_matches equivalent pattern term)

theorem closed_matches_exact (equivalent : Pattern → Pattern → Bool)
    (pattern term : Pattern) (budget : Nat)
    (closed : (state equivalent pattern term budget).closed = true) :
    (state equivalent pattern term budget).outputs = matchPatternWith equivalent pattern term :=
  (closed_readout _ _ closed).trans (flatten_matches equivalent pattern term)

theorem effective_completion (equivalent : Pattern → Pattern → Bool) (pattern term : Pattern) :
    (state equivalent pattern term (patternMatches equivalent pattern term).workBound).closed = true :=
  run_closed_at _ _ (Nat.le_refl _)

end Mettapedia.OSLF.NativeTypes.Decision.Structural.Matching
