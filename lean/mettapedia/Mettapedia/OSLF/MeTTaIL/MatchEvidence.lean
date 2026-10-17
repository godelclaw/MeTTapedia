import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mathlib.Data.List.ProdSigma

/-!
# Explicit choice evidence for structural matching

This operational layer checks one supplied path through the independently
specified MeTTaIL matcher. A trace records the residual target index selected
at each unordered collection site. Replay checks constructor shape, binder
arity, ordered arguments, vector remainders and repeated-variable agreement,
while following the supplied choices instead of enumerating alternatives.

The guided source judgments retain each choice and erase to `MatchSpec`.
Replay is exact for those judgments, and every original matching derivation
has accepted finite guidance. Choice count is bounded by source-pattern size;
executed machine time requires a separate resource account.
-/

namespace Mettapedia.OSLF.MeTTaIL.MatchEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec

/-- Merge two consecutive guided replay results without exploring alternatives. -/
def joinReplay (first : Option (Bindings × List Nat))
    (next : List Nat → Option (Bindings × List Nat)) : Option (Bindings × List Nat) :=
  match first with
  | none => none
  | some (head, middle) =>
      match next middle with
      | none => none
      | some (tail, final) => (mergeBindings head tail).map (fun bindings => (bindings, final))

theorem joinReplay_eq_some_iff (first : Option (Bindings × List Nat))
    (next : List Nat → Option (Bindings × List Nat))
    (bindings : Bindings) (remaining : List Nat) :
    joinReplay first next = some (bindings, remaining) ↔
      ∃ head middle tail, first = some (head, middle) ∧
        next middle = some (tail, remaining) ∧ mergeBindings head tail = some bindings := by
  cases first with
  | none => simp [joinReplay]
  | some pair =>
      rcases pair with ⟨head, middle⟩
      cases nextCase : next middle with
      | none => simp [joinReplay, nextCase]
      | some pair =>
          rcases pair with ⟨tail, final⟩
          simp [joinReplay, nextCase, Option.map_eq_some_iff, and_assoc, and_comm]

/- A trace gives the residual target position chosen at each unordered
matching site. Every other structural check remains part of replay. -/
mutual

def replayArguments : List Pattern → List Pattern → List Nat → Option (Bindings × List Nat)
  | [], [], trace => some ([], trace)
  | pattern :: patterns, target :: targets, trace =>
      joinReplay (replayPattern pattern target trace)
        (fun remaining => replayArguments patterns targets remaining)
  | _, _, _ => none
termination_by patterns => sizeOf patterns
decreasing_by all_goals sizeOf_pattern_dec

def replayBag : List Pattern → Option String → CollType → List Pattern →
    List Nat → Option (Bindings × List Nat)
  | [], none, _, [], trace => some ([], trace)
  | [], none, _, _ :: _, _ => none
  | [], some name, kind, targets, trace =>
      some ([(name, .collection kind targets none)], trace)
  | pattern :: patterns, rest, kind, targets, index :: trace =>
      match targets[index]? with
      | none => none
      | some target =>
          joinReplay (replayPattern pattern target trace)
            (fun remaining => replayBag patterns rest kind (targets.eraseIdx index) remaining)
  | _ :: _, _, _, _, [] => none
termination_by patterns => sizeOf patterns
decreasing_by all_goals sizeOf_pattern_dec

def replayPattern (pattern target : Pattern) (trace : List Nat) : Option (Bindings × List Nat) :=
  match pattern, target with
  | .fvar name, value => some ([(name, value)], trace)
  | .bvar left, .bvar right => if left == right then some ([], trace) else none
  | .apply left patterns, .apply right targets =>
      if left == right && patterns.length == targets.length then
        replayArguments patterns targets trace
      else none
  | .lambda _ body, .lambda _ actual => replayPattern body actual trace
  | .multiLambda arity _ body, .multiLambda actualArity _ actual =>
      if arity == actualArity then replayPattern body actual trace else none
  | .collection kind patterns rest, .collection actualKind targets _ =>
      if kind == actualKind then
        if kind == .vec then
          match rest with
          | none => replayArguments patterns targets trace
          | some name =>
              joinReplay (replayArguments patterns (targets.take patterns.length) trace)
                (fun remaining => some ([(name, .collection .vec (targets.drop patterns.length) none)], remaining))
        else replayBag patterns rest kind targets trace
      else none
  | .subst body replacement, .subst actualBody actualReplacement =>
      joinReplay (replayPattern body actualBody trace)
        (fun remaining => replayPattern replacement actualReplacement remaining)
  | _, _ => none
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

end

/-- Unordered collection replay uses precisely the explicitly guided bag
operation after the common kind check. -/
theorem replayPattern_collection_unordered (kind : CollType) (patterns targets : List Pattern)
    (rest actualRest : Option String) (trace : List Nat) (notVector : kind ≠ .vec) :
    replayPattern (.collection kind patterns rest) (.collection kind targets actualRest) trace =
      replayBag patterns rest kind targets trace := by
  rw [replayPattern.eq_def]
  simp [notVector]

mutual

/-- Every independently valid matching derivation has finite guidance which
the replay checker accepts without searching for bag permutations. -/
theorem replayPattern_complete {pattern target : Pattern} {bindings : Bindings}
    (matched : MatchRel pattern target bindings) :
    ∃ trace, ∀ suffix, replayPattern pattern target (trace ++ suffix) = some (bindings, suffix) := by
  cases matched with
  | fvar => exact ⟨[], fun suffix => by simp [replayPattern]⟩
  | bvar => exact ⟨[], fun suffix => by simp [replayPattern]⟩
  | apply arguments sameLength =>
      obtain ⟨trace, replayed⟩ := replayArguments_complete arguments
      exact ⟨trace, fun suffix => by simp [replayPattern, sameLength, replayed suffix]⟩
  | lambda body =>
      obtain ⟨trace, replayed⟩ := replayPattern_complete body
      exact ⟨trace, fun suffix => by simpa [replayPattern] using replayed suffix⟩
  | multiLambda body =>
      obtain ⟨trace, replayed⟩ := replayPattern_complete body
      exact ⟨trace, fun suffix => by simpa [replayPattern] using replayed suffix⟩
  | collection notVector elements =>
      obtain ⟨trace, replayed⟩ := replayBag_complete elements
      exact ⟨trace, fun suffix => by rw [replayPattern_collection_unordered _ _ _ _ _ _ notVector]; exact replayed suffix⟩
  | vector arguments =>
      obtain ⟨trace, replayed⟩ := replayArguments_complete arguments
      exact ⟨trace, fun suffix => by simpa [replayPattern] using replayed suffix⟩
  | vectorRest prefixMatched merged =>
      obtain ⟨trace, replayed⟩ := replayArguments_complete prefixMatched
      exact ⟨trace, fun suffix => by simp [replayPattern, replayed suffix, merged, joinReplay]⟩
  | subst body replacement merged =>
      obtain ⟨bodyTrace, bodyReplayed⟩ := replayPattern_complete body
      obtain ⟨replacementTrace, replacementReplayed⟩ := replayPattern_complete replacement
      refine ⟨bodyTrace ++ replacementTrace, ?_⟩
      intro suffix
      simp [List.append_assoc, replayPattern, bodyReplayed, replacementReplayed, merged, joinReplay]

theorem replayArguments_complete {patterns targets : List Pattern} {bindings : Bindings}
    (matched : MatchArgsRel patterns targets bindings) :
    ∃ trace, ∀ suffix, replayArguments patterns targets (trace ++ suffix) = some (bindings, suffix) := by
  cases matched with
  | nil => exact ⟨[], fun suffix => by simp [replayArguments]⟩
  | cons head tail merged =>
      obtain ⟨headTrace, headReplayed⟩ := replayPattern_complete head
      obtain ⟨tailTrace, tailReplayed⟩ := replayArguments_complete tail
      refine ⟨headTrace ++ tailTrace, ?_⟩
      intro suffix
      simp [List.append_assoc, replayArguments, headReplayed, tailReplayed, merged, joinReplay]

theorem replayBag_complete {patterns targets : List Pattern}
    {rest : Option String} {kind : CollType} {bindings : Bindings}
    (matched : MatchBagRel patterns rest kind targets bindings) :
    ∃ trace, ∀ suffix, replayBag patterns rest kind targets (trace ++ suffix) = some (bindings, suffix) := by
  cases matched with
  | nilNoRest => exact ⟨[], fun suffix => by simp [replayBag]⟩
  | nilRest => exact ⟨[], fun suffix => by simp [replayBag]⟩
  | cons index within head tail merged =>
      obtain ⟨headTrace, headReplayed⟩ := replayPattern_complete head
      obtain ⟨tailTrace, tailReplayed⟩ := replayBag_complete tail
      refine ⟨index :: (headTrace ++ tailTrace), ?_⟩
      intro suffix
      simp [List.append_assoc, replayBag, within, headReplayed, tailReplayed, merged, joinReplay]

end

/- The following relations retain the choice data of the existing matching
rules. They are independent of replay and erase to the original MatchSpec
judgments. Input and remaining trace are explicit to support composition. -/
mutual

inductive GuidedMatchRel : Pattern → Pattern → Bindings → List Nat → List Nat → Prop where
  | fvar : GuidedMatchRel (.fvar name) value [(name, value)] trace trace
  | bvar : GuidedMatchRel (.bvar index) (.bvar index) [] trace trace
  | apply :
      GuidedArgumentsRel patterns targets bindings trace remaining →
      patterns.length = targets.length →
      GuidedMatchRel (.apply label patterns) (.apply label targets) bindings trace remaining
  | lambda :
      GuidedMatchRel body actual bindings trace remaining →
      GuidedMatchRel (.lambda display body) (.lambda actualDisplay actual) bindings trace remaining
  | multiLambda :
      GuidedMatchRel body actual bindings trace remaining →
      GuidedMatchRel (.multiLambda arity displays body) (.multiLambda arity actualDisplays actual)
        bindings trace remaining
  | collection :
      kind ≠ .vec →
      GuidedBagRel patterns rest kind targets bindings trace remaining →
      GuidedMatchRel (.collection kind patterns rest) (.collection kind targets actualRest)
        bindings trace remaining
  | vector :
      GuidedArgumentsRel patterns targets bindings trace remaining →
      GuidedMatchRel (.collection .vec patterns none) (.collection .vec targets actualRest)
        bindings trace remaining
  | vectorRest :
      GuidedArgumentsRel patterns (targets.take patterns.length) prefixBindings trace remaining →
      mergeBindings prefixBindings [(name, .collection .vec (targets.drop patterns.length) none)] = some bindings →
      GuidedMatchRel (.collection .vec patterns (some name)) (.collection .vec targets actualRest)
        bindings trace remaining
  | subst :
      GuidedMatchRel body actualBody bodyBindings trace middle →
      GuidedMatchRel replacement actualReplacement replacementBindings middle remaining →
      mergeBindings bodyBindings replacementBindings = some bindings →
      GuidedMatchRel (.subst body replacement) (.subst actualBody actualReplacement)
        bindings trace remaining

inductive GuidedArgumentsRel : List Pattern → List Pattern → Bindings → List Nat → List Nat → Prop where
  | nil : GuidedArgumentsRel [] [] [] trace trace
  | cons :
      GuidedMatchRel pattern target headBindings trace middle →
      GuidedArgumentsRel patterns targets tailBindings middle remaining →
      mergeBindings headBindings tailBindings = some bindings →
      GuidedArgumentsRel (pattern :: patterns) (target :: targets) bindings trace remaining

inductive GuidedBagRel : List Pattern → Option String → CollType → List Pattern →
    Bindings → List Nat → List Nat → Prop where
  | nilNoRest : GuidedBagRel [] none kind [] [] trace trace
  | nilRest : GuidedBagRel [] (some name) kind targets [(name, .collection kind targets none)] trace trace
  | cons :
      (index : Nat) → (within : index < targets.length) →
      GuidedMatchRel pattern targets[index] headBindings trace middle →
      GuidedBagRel patterns rest kind (targets.eraseIdx index) tailBindings middle remaining →
      mergeBindings headBindings tailBindings = some bindings →
      GuidedBagRel (pattern :: patterns) rest kind targets bindings (index :: trace) remaining

end

mutual

theorem GuidedMatchRel.erase {pattern target : Pattern} {bindings : Bindings}
    {trace remaining : List Nat} (matched : GuidedMatchRel pattern target bindings trace remaining) :
    MatchRel pattern target bindings := by
  cases matched with
  | fvar => exact .fvar
  | bvar => exact .bvar
  | apply arguments sameLength => exact .apply arguments.erase sameLength
  | lambda body => exact .lambda body.erase
  | multiLambda body => exact .multiLambda body.erase
  | collection notVector elements => exact .collection notVector elements.erase
  | vector arguments => exact .vector arguments.erase
  | vectorRest prefixMatched merged => exact .vectorRest prefixMatched.erase merged
  | subst body replacement merged => exact .subst body.erase replacement.erase merged

theorem GuidedArgumentsRel.erase {patterns targets : List Pattern} {bindings : Bindings}
    {trace remaining : List Nat} (matched : GuidedArgumentsRel patterns targets bindings trace remaining) :
    MatchArgsRel patterns targets bindings := by
  cases matched with
  | nil => exact .nil
  | cons head tail merged => exact .cons head.erase tail.erase merged

theorem GuidedBagRel.erase {patterns targets : List Pattern} {rest : Option String}
    {kind : CollType} {bindings : Bindings} {trace remaining : List Nat}
    (matched : GuidedBagRel patterns rest kind targets bindings trace remaining) :
    MatchBagRel patterns rest kind targets bindings := by
  cases matched with
  | nilNoRest => exact .nilNoRest
  | nilRest => exact .nilRest
  | cons index within head tail merged => exact .cons index within head.erase tail.erase merged

end

mutual

theorem replayPattern_guided (pattern target : Pattern) (trace : List Nat)
    {bindings : Bindings} {remaining : List Nat}
    (replayed : replayPattern pattern target trace = some (bindings, remaining)) :
    GuidedMatchRel pattern target bindings trace remaining := by
  match pattern, target with
  | .fvar name, value =>
      simp only [replayPattern, Option.some.injEq, Prod.mk.injEq] at replayed
      rcases replayed with ⟨rfl, rfl⟩
      exact .fvar
  | .bvar left, .bvar right =>
      by_cases same : left = right
      · subst right
        simp only [replayPattern, beq_self_eq_true, ↓reduceIte,
          Option.some.injEq, Prod.mk.injEq] at replayed
        rcases replayed with ⟨rfl, rfl⟩
        exact .bvar
      · simp [replayPattern, same] at replayed
  | .apply left patterns, .apply right targets =>
      by_cases same : left = right
      · subst right
        by_cases sameLength : patterns.length = targets.length
        · have arguments : replayArguments patterns targets trace = some (bindings, remaining) := by
            simpa only [replayPattern, beq_self_eq_true, Bool.true_and,
              beq_iff_eq.mpr sameLength, ↓reduceIte] using replayed
          exact .apply (replayArguments_guided patterns targets trace arguments) sameLength
        · simp [replayPattern, sameLength] at replayed
      · simp [replayPattern, same] at replayed
  | .lambda display body, .lambda actualDisplay actual =>
      exact .lambda (replayPattern_guided body actual trace (by simpa only [replayPattern] using replayed))
  | .multiLambda arity display body, .multiLambda actualArity actualDisplay actual =>
      by_cases same : arity = actualArity
      · subst actualArity
        exact .multiLambda (replayPattern_guided body actual trace (by simpa [replayPattern] using replayed))
      · simp [replayPattern, same] at replayed
  | .collection kind patterns rest, .collection actualKind targets actualRest =>
      by_cases same : kind = actualKind
      · subst actualKind
        by_cases vector : kind = .vec
        · subst kind
          cases rest with
          | none =>
              exact .vector (replayArguments_guided patterns targets trace
                (by simpa only [replayPattern, beq_self_eq_true, ↓reduceIte] using replayed))
          | some name =>
              simp only [replayPattern, beq_self_eq_true, ↓reduceIte] at replayed
              obtain ⟨prefixBindings, final, restBindings, prefixReplay, returned, merged⟩ :=
                (joinReplay_eq_some_iff _ _ _ _).mp replayed
              simp only [Option.some.injEq, Prod.mk.injEq] at returned
              rcases returned with ⟨rfl, rfl⟩
              exact .vectorRest (replayArguments_guided _ _ _ prefixReplay) merged
        · rw [replayPattern_collection_unordered _ _ _ _ _ _ vector] at replayed
          exact .collection vector (replayBag_guided patterns rest kind targets trace replayed)
      · rw [replayPattern.eq_def] at replayed
        simp [same] at replayed
  | .subst body replacement, .subst actualBody actualReplacement =>
      simp only [replayPattern] at replayed
      obtain ⟨bodyBindings, middle, replacementBindings, bodyReplay, replacementReplay, merged⟩ :=
        (joinReplay_eq_some_iff _ _ _ _).mp replayed
      exact .subst (replayPattern_guided _ _ _ bodyReplay)
        (replayPattern_guided _ _ _ replacementReplay) merged
  | .bvar _, .fvar _
  | .bvar _, .apply _ _
  | .bvar _, .lambda _ _
  | .bvar _, .multiLambda _ _ _
  | .bvar _, .collection _ _ _
  | .bvar _, .subst _ _ =>
      rw [replayPattern.eq_def] at replayed
      simp at replayed
  | .apply _ _, .fvar _
  | .apply _ _, .bvar _
  | .apply _ _, .lambda _ _
  | .apply _ _, .multiLambda _ _ _
  | .apply _ _, .collection _ _ _
  | .apply _ _, .subst _ _ =>
      rw [replayPattern.eq_def] at replayed
      simp at replayed
  | .lambda _ _, .fvar _
  | .lambda _ _, .bvar _
  | .lambda _ _, .apply _ _
  | .lambda _ _, .multiLambda _ _ _
  | .lambda _ _, .collection _ _ _
  | .lambda _ _, .subst _ _ =>
      rw [replayPattern.eq_def] at replayed
      simp at replayed
  | .multiLambda _ _ _, .fvar _
  | .multiLambda _ _ _, .bvar _
  | .multiLambda _ _ _, .apply _ _
  | .multiLambda _ _ _, .lambda _ _
  | .multiLambda _ _ _, .collection _ _ _
  | .multiLambda _ _ _, .subst _ _ =>
      rw [replayPattern.eq_def] at replayed
      simp at replayed
  | .collection _ _ _, .fvar _
  | .collection _ _ _, .bvar _
  | .collection _ _ _, .apply _ _
  | .collection _ _ _, .lambda _ _
  | .collection _ _ _, .multiLambda _ _ _
  | .collection _ _ _, .subst _ _ =>
      rw [replayPattern.eq_def] at replayed
      simp at replayed
  | .subst _ _, .fvar _
  | .subst _ _, .bvar _
  | .subst _ _, .apply _ _
  | .subst _ _, .lambda _ _
  | .subst _ _, .multiLambda _ _ _
  | .subst _ _, .collection _ _ _ =>
      rw [replayPattern.eq_def] at replayed
      simp at replayed
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem replayArguments_guided (patterns targets : List Pattern) (trace : List Nat)
    {bindings : Bindings} {remaining : List Nat}
    (replayed : replayArguments patterns targets trace = some (bindings, remaining)) :
    GuidedArgumentsRel patterns targets bindings trace remaining := by
  cases patterns with
  | nil =>
      cases targets with
      | nil =>
          simp only [replayArguments, Option.some.injEq, Prod.mk.injEq] at replayed
          rcases replayed with ⟨rfl, rfl⟩
          exact .nil
      | cons => simp [replayArguments] at replayed
  | cons pattern patterns =>
      cases targets with
      | nil => simp [replayArguments] at replayed
      | cons target targets =>
          simp only [replayArguments] at replayed
          obtain ⟨headBindings, middle, tailBindings, headReplay, tailReplay, merged⟩ :=
            (joinReplay_eq_some_iff _ _ _ _).mp replayed
          exact .cons (replayPattern_guided _ _ _ headReplay)
            (replayArguments_guided _ _ _ tailReplay) merged
termination_by sizeOf patterns
decreasing_by all_goals sizeOf_pattern_dec

theorem replayBag_guided (patterns : List Pattern) (rest : Option String)
    (kind : CollType) (targets : List Pattern) (trace : List Nat)
    {bindings : Bindings} {remaining : List Nat}
    (replayed : replayBag patterns rest kind targets trace = some (bindings, remaining)) :
    GuidedBagRel patterns rest kind targets bindings trace remaining := by
  cases patterns with
  | nil =>
      cases rest with
      | none =>
          cases targets with
          | nil =>
              simp only [replayBag, Option.some.injEq, Prod.mk.injEq] at replayed
              rcases replayed with ⟨rfl, rfl⟩
              exact .nilNoRest
          | cons => simp [replayBag] at replayed
      | some name =>
          simp only [replayBag, Option.some.injEq, Prod.mk.injEq] at replayed
          rcases replayed with ⟨rfl, rfl⟩
          exact .nilRest
  | cons pattern patterns =>
      cases trace with
      | nil => simp [replayBag] at replayed
      | cons index trace =>
          cases selected : targets[index]? with
          | none => simp [replayBag, selected] at replayed
          | some target =>
              simp only [replayBag, selected] at replayed
              obtain ⟨headBindings, middle, tailBindings, headReplay, tailReplay, merged⟩ :=
                (joinReplay_eq_some_iff _ _ _ _).mp replayed
              obtain ⟨within, sameTarget⟩ := List.getElem?_eq_some_iff.mp selected
              subst target
              exact .cons index within (replayPattern_guided _ _ _ headReplay)
                (replayBag_guided _ _ _ _ _ tailReplay) merged
termination_by sizeOf patterns
decreasing_by all_goals sizeOf_pattern_dec

end

mutual

theorem GuidedMatchRel.replay {pattern target : Pattern} {bindings : Bindings}
    {trace remaining : List Nat} (matched : GuidedMatchRel pattern target bindings trace remaining) :
    replayPattern pattern target trace = some (bindings, remaining) := by
  cases matched with
  | fvar => simp [replayPattern]
  | bvar => simp [replayPattern]
  | apply arguments sameLength => simp [replayPattern, sameLength, arguments.replay]
  | lambda body => simpa only [replayPattern] using body.replay
  | multiLambda body => simpa [replayPattern] using body.replay
  | collection notVector elements =>
      rw [replayPattern_collection_unordered _ _ _ _ _ _ notVector]
      exact elements.replay
  | vector arguments => simpa [replayPattern] using arguments.replay
  | vectorRest prefixMatched merged =>
      simp [replayPattern, prefixMatched.replay, joinReplay, merged]
  | subst body replacement merged =>
      simp [replayPattern, body.replay, replacement.replay, joinReplay, merged]

theorem GuidedArgumentsRel.replay {patterns targets : List Pattern} {bindings : Bindings}
    {trace remaining : List Nat} (matched : GuidedArgumentsRel patterns targets bindings trace remaining) :
    replayArguments patterns targets trace = some (bindings, remaining) := by
  cases matched with
  | nil => simp [replayArguments]
  | cons head tail merged => simp [replayArguments, head.replay, tail.replay, joinReplay, merged]

theorem GuidedBagRel.replay {patterns targets : List Pattern} {rest : Option String}
    {kind : CollType} {bindings : Bindings} {trace remaining : List Nat}
    (matched : GuidedBagRel patterns rest kind targets bindings trace remaining) :
    replayBag patterns rest kind targets trace = some (bindings, remaining) := by
  cases matched with
  | nilNoRest => simp [replayBag]
  | nilRest => simp [replayBag]
  | cons index within head tail merged =>
      simp [replayBag, within, head.replay, tail.replay, joinReplay, merged]

end

theorem replayPattern_sound (pattern target : Pattern) (trace : List Nat)
    {bindings : Bindings} {remaining : List Nat}
    (replayed : replayPattern pattern target trace = some (bindings, remaining)) :
    MatchRel pattern target bindings :=
  (replayPattern_guided pattern target trace replayed).erase

/-- Checking consumes every submitted choice.  It never invokes the search
matcher or computes its whole answer bag. -/
def checkGuidedMatch (pattern target : Pattern) (bindings : Bindings) (trace : List Nat) : Bool :=
  decide (replayPattern pattern target trace = some (bindings, []))

@[simp] theorem checkGuidedMatch_exact (pattern target : Pattern) (bindings : Bindings) (trace : List Nat) :
    checkGuidedMatch pattern target bindings trace = true ↔
      GuidedMatchRel pattern target bindings trace [] := by
  simp only [checkGuidedMatch, decide_eq_true_eq]
  exact ⟨replayPattern_guided pattern target trace, GuidedMatchRel.replay⟩

theorem matchRel_iff_exists_guidance (pattern target : Pattern) (bindings : Bindings) :
    MatchRel pattern target bindings ↔ ∃ trace, checkGuidedMatch pattern target bindings trace = true := by
  constructor
  · intro matched
    obtain ⟨trace, replayed⟩ := replayPattern_complete matched
    refine ⟨trace, ?_⟩
    simp only [checkGuidedMatch, decide_eq_true_eq]
    simpa only [List.append_nil] using replayed []
  · rintro ⟨trace, accepted⟩
    exact ((checkGuidedMatch_exact pattern target bindings trace).mp accepted).erase

theorem matchPattern_mem_iff_exists_guidance (pattern target : Pattern) (bindings : Bindings) :
    bindings ∈ matchPattern pattern target ↔ ∃ trace, checkGuidedMatch pattern target bindings trace = true := by
  rw [matchPattern_iff_matchRel, matchRel_iff_exists_guidance]

mutual

/-- An accepted guidance word contains at most one position per structural
matching site. This bounds choice count, not executed checker time. -/
theorem GuidedMatchRel.traceLength {pattern target : Pattern} {bindings : Bindings}
    {trace remaining : List Nat} (matched : GuidedMatchRel pattern target bindings trace remaining) :
    trace.length ≤ remaining.length + sizeOf pattern := by
  cases matched with
  | fvar => omega
  | bvar => omega
  | apply arguments _ =>
      have bound := arguments.traceLength
      simp_wf
      omega
  | lambda body =>
      have bound := body.traceLength
      simp_wf
      omega
  | multiLambda body =>
      have bound := body.traceLength
      simp_wf
      omega
  | collection _ elements =>
      have bound := elements.traceLength
      simp_wf
      omega
  | vector arguments =>
      have bound := arguments.traceLength
      simp_wf
      omega
  | vectorRest prefixMatched _ =>
      have bound := prefixMatched.traceLength
      simp_wf
      omega
  | subst body replacement _ =>
      have first := body.traceLength
      have second := replacement.traceLength
      simp_wf
      omega

theorem GuidedArgumentsRel.traceLength {patterns targets : List Pattern} {bindings : Bindings}
    {trace remaining : List Nat} (matched : GuidedArgumentsRel patterns targets bindings trace remaining) :
    trace.length ≤ remaining.length + sizeOf patterns := by
  cases matched with
  | nil => omega
  | cons head tail _ =>
      have first := head.traceLength
      have second := tail.traceLength
      simp_wf
      omega

theorem GuidedBagRel.traceLength {patterns targets : List Pattern} {rest : Option String}
    {kind : CollType} {bindings : Bindings} {trace remaining : List Nat}
    (matched : GuidedBagRel patterns rest kind targets bindings trace remaining) :
    trace.length ≤ remaining.length + sizeOf patterns := by
  cases matched with
  | nilNoRest => omega
  | nilRest => omega
  | cons index within head tail merged =>
      have first := head.traceLength
      have second := tail.traceLength
      simp only [List.length_cons]
      simp_wf
      omega

end

theorem accepted_guidance_length_le (pattern target : Pattern) (bindings : Bindings) (trace : List Nat)
    (accepted : checkGuidedMatch pattern target bindings trace = true) :
    trace.length ≤ sizeOf pattern := by
  have bound := ((checkGuidedMatch_exact pattern target bindings trace).mp accepted).traceLength
  simpa using bound

theorem GuidedMatchRel.deterministic {pattern target : Pattern}
    {firstBindings secondBindings : Bindings} {trace firstRemaining secondRemaining : List Nat}
    (first : GuidedMatchRel pattern target firstBindings trace firstRemaining)
    (second : GuidedMatchRel pattern target secondBindings trace secondRemaining) :
    firstBindings = secondBindings ∧ firstRemaining = secondRemaining := by
  have same := first.replay.symm.trans second.replay
  simpa only [Option.some.injEq, Prod.mk.injEq] using same

namespace GuidedControls

def atomA : Pattern := .apply "a" []
def atomB : Pattern := .apply "b" []
def pairPattern : Pattern := .collection .hashBag [.fvar "x", .fvar "y"] none
def duplicateTarget : Pattern := .collection .hashBag [atomA, atomA] none
def duplicateBindings : Bindings := [("y", atomA), ("x", atomA)]

theorem first_duplicate_choice_accepted :
    checkGuidedMatch pairPattern duplicateTarget duplicateBindings [0, 0] = true := by decide +kernel

theorem second_duplicate_choice_accepted :
    checkGuidedMatch pairPattern duplicateTarget duplicateBindings [1, 0] = true := by decide +kernel

theorem original_matcher_retains_both_choices :
    (matchPattern pairPattern duplicateTarget).count duplicateBindings = 2 := by
  decide +kernel

theorem absent_choice_rejected :
    checkGuidedMatch pairPattern duplicateTarget duplicateBindings [] = false := by decide +kernel

theorem out_of_bounds_choice_rejected :
    checkGuidedMatch pairPattern duplicateTarget duplicateBindings [2, 0] = false := by decide +kernel

theorem unused_choice_rejected :
    checkGuidedMatch pairPattern duplicateTarget duplicateBindings [0, 0, 99] = false := by decide +kernel

theorem inconsistent_repeated_variable_rejected :
    checkGuidedMatch (.apply "Pair" [.fvar "x", .fvar "x"])
      (.apply "Pair" [atomA, atomB]) [("x", atomA)] [] = false := by decide +kernel

theorem binder_metadata_preserves_source_matching :
    checkGuidedMatch (.lambda (some "source") (.fvar "x"))
      (.lambda (some "target") (.bvar 0)) [("x", .bvar 0)] [] = true := by decide +kernel

theorem wrong_binder_arity_rejected :
    checkGuidedMatch (.multiLambda 1 [] (.fvar "x"))
      (.multiLambda 2 [] (.bvar 0)) [("x", .bvar 0)] [] = false := by decide +kernel

theorem vector_order_preserved :
    checkGuidedMatch (.collection .vec [atomA, atomB] none)
      (.collection .vec [atomB, atomA] none) [] [] = false := by decide +kernel

theorem vector_remainder_accepted :
    checkGuidedMatch (.collection .vec [.fvar "x"] (some "rest"))
      (.collection .vec [atomA, atomB] none)
      [("rest", .collection .vec [atomB] none), ("x", atomA)] [] = true := by decide +kernel

theorem explicit_substitution_is_matched_structurally :
    checkGuidedMatch (.subst (.fvar "x") (.fvar "y")) (.subst atomA atomB)
      [("y", atomB), ("x", atomA)] [] = true := by decide +kernel

end GuidedControls


/-! ## Occurrence-preserving guidance construction -/

/-- Instrumented construction joins exact matcher branches and their choice
words. It is a proof producer, separate from guided checking. -/
def mergeGuidedRows (heads tails : List (Bindings × List Nat)) : List (Bindings × List Nat) :=
  heads.flatMap fun head => tails.filterMap fun tail =>
    (mergeBindings head.1 tail.1).map fun bindings => (bindings, head.2 ++ tail.2)

theorem project_mergeGuidedRows (heads tails : List (Bindings × List Nat)) :
    (mergeGuidedRows heads tails).map Prod.fst =
      (heads.map Prod.fst).flatMap fun head => (tails.map Prod.fst).filterMap (mergeBindings head) := by
  simp only [mergeGuidedRows, List.map_flatMap, List.flatMap_map, List.map_filterMap,
    List.filterMap_map, Option.map_map, Function.comp_def, Option.map_id']

mutual

def enumerateArguments : List Pattern → List Pattern → List (Bindings × List Nat)
  | [], [] => [([], [])]
  | pattern :: patterns, target :: targets =>
      mergeGuidedRows (enumeratePattern pattern target) (enumerateArguments patterns targets)
  | _, _ => []
termination_by patterns => sizeOf patterns
decreasing_by all_goals sizeOf_pattern_dec

def enumerateBag : List Pattern → Option String → CollType → List Pattern →
    List (Bindings × List Nat)
  | [], none, _, [] => [([], [])]
  | [], none, _, _ :: _ => []
  | [], some name, kind, targets => [([(name, .collection kind targets none)], [])]
  | pattern :: patterns, rest, kind, targets =>
      targets.zipIdx.flatMap fun (target, index) =>
        (mergeGuidedRows (enumeratePattern pattern target)
          (enumerateBag patterns rest kind (targets.eraseIdx index))).map
            fun row => (row.1, index :: row.2)
termination_by patterns => sizeOf patterns
decreasing_by all_goals sizeOf_pattern_dec

def enumeratePattern (pattern target : Pattern) : List (Bindings × List Nat) :=
  match pattern, target with
  | .fvar name, value => [([(name, value)], [])]
  | .bvar left, .bvar right => if left == right then [([], [])] else []
  | .apply left patterns, .apply right targets =>
      if left == right && patterns.length == targets.length then
        enumerateArguments patterns targets
      else []
  | .lambda _ body, .lambda _ actual => enumeratePattern body actual
  | .multiLambda arity _ body, .multiLambda actualArity _ actual =>
      if arity == actualArity then enumeratePattern body actual else []
  | .collection kind patterns rest, .collection actualKind targets _ =>
      if kind == actualKind then
        if kind == .vec then
          match rest with
          | none => enumerateArguments patterns targets
          | some name => mergeGuidedRows (enumerateArguments patterns (targets.take patterns.length))
              [([(name, .collection .vec (targets.drop patterns.length) none)], [])]
        else enumerateBag patterns rest kind targets
      else []
  | .subst body replacement, .subst actualBody actualReplacement =>
      mergeGuidedRows (enumeratePattern body actualBody) (enumeratePattern replacement actualReplacement)
  | _, _ => []
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

end

private theorem merge_singleton_filterMap (values : List Bindings) (extra : Bindings) :
    values.flatMap (fun value => [extra].filterMap (mergeBindings value)) =
      values.filterMap (fun value => mergeBindings value extra) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      cases found : mergeBindings value extra <;> simp [List.flatMap_cons, found, ih]

private theorem enumerateArguments_project_of (patterns targets : List Pattern)
    (pointwise : ∀ pattern ∈ patterns, ∀ target,
      (enumeratePattern pattern target).map Prod.fst = matchPattern pattern target) :
    (enumerateArguments patterns targets).map Prod.fst = matchArgs patterns targets := by
  induction patterns generalizing targets with
  | nil => cases targets <;> simp [enumerateArguments, matchArgs]
  | cons pattern patterns ih =>
      cases targets with
      | nil => simp [enumerateArguments, matchArgs]
      | cons target targets =>
          have head := pointwise pattern (by simp) target
          have tail := ih targets (fun child member => pointwise child (by simp [member]))
          simp [enumerateArguments, matchArgs, project_mergeGuidedRows, head, tail]

private theorem enumerateBag_project_of (patterns : List Pattern) (rest : Option String)
    (kind : CollType) (targets : List Pattern)
    (pointwise : ∀ pattern ∈ patterns, ∀ target,
      (enumeratePattern pattern target).map Prod.fst = matchPattern pattern target) :
    (enumerateBag patterns rest kind targets).map Prod.fst = matchBag patterns rest kind targets := by
  induction patterns generalizing targets with
  | nil => cases rest <;> cases targets <;> simp [enumerateBag, matchBag]
  | cons pattern patterns ih =>
      have head := pointwise pattern (by simp)
      have tail := fun targets => ih targets (fun child member => pointwise child (by simp [member]))
      simp only [enumerateBag, matchBag, List.map_flatMap, List.map_map]
      apply List.flatMap_congr
      intro pair _member
      rcases pair with ⟨target, index⟩
      simpa [Function.comp_def] using
        (project_mergeGuidedRows (enumeratePattern pattern target)
          (enumerateBag patterns rest kind (targets.eraseIdx index))).trans
            (by rw [head target, tail])

/-- Erasing guidance preserves the complete original answer list, hence
its occurrence multiplicities. Construction may search; checking one submitted
path uses only `replayPattern`. -/
theorem enumeratePattern_project (pattern target : Pattern) :
    (enumeratePattern pattern target).map Prod.fst = matchPattern pattern target := by
  induction pattern using Pattern.inductionOn generalizing target with
  | hbvar index =>
      cases target <;> try simp [enumeratePattern, matchPattern]
      case bvar actual =>
        by_cases same : index = actual <;> simp [same]
  | hfvar name => simp [enumeratePattern, matchPattern]
  | happly label patterns ih =>
      have arguments := fun targets => enumerateArguments_project_of patterns targets ih
      cases target <;> try simp [enumeratePattern, matchPattern]
      case apply actual targets =>
        by_cases admitted : label = actual ∧ patterns.length = targets.length
        · simp [admitted.1, admitted.2, arguments]
        · simp [admitted]
  | hlambda display body ih =>
      cases target <;> simp [enumeratePattern, matchPattern, ih]
  | hmultiLambda arity displays body ih =>
      cases target <;> try simp [enumeratePattern, matchPattern]
      case multiLambda actualArity actualDisplays actual =>
        by_cases same : arity = actualArity <;> simp [same, ih]
  | hsubst body replacement ihBody ihReplacement =>
      cases target <;> simp [enumeratePattern, matchPattern, project_mergeGuidedRows, ihBody, ihReplacement]
  | hcollection kind patterns rest ih =>
      have arguments := fun targets => enumerateArguments_project_of patterns targets ih
      have bag := fun targets => enumerateBag_project_of patterns rest kind targets ih
      cases target <;> try simp [enumeratePattern.eq_def, matchPattern.eq_def]
      case collection actualKind targets actualRest =>
        by_cases same : kind = actualKind
        · subst actualKind
          by_cases vector : kind = .vec
          · subst kind
            cases rest <;> simp [project_mergeGuidedRows, arguments, merge_singleton_filterMap]
          · simp [vector, bag]
        · simp [same]

theorem mem_mergeGuidedRows (heads tails : List (Bindings × List Nat))
    (row : Bindings × List Nat) :
    row ∈ mergeGuidedRows heads tails ↔
      ∃ head ∈ heads, ∃ tail ∈ tails,
        mergeBindings head.1 tail.1 = some row.1 ∧ row.2 = head.2 ++ tail.2 := by
  rcases row with ⟨bindings, trace⟩
  simp only [mergeGuidedRows, List.mem_flatMap, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨head, headMember, tail, tailMember, merged, mergedEq, returned⟩
    simp only [Prod.mk.injEq] at returned
    rcases returned with ⟨rfl, rfl⟩
    exact ⟨head, headMember, tail, tailMember, mergedEq, rfl⟩
  · rintro ⟨head, headMember, tail, tailMember, mergedEq, traceEq⟩
    exact ⟨head, headMember, tail, tailMember, bindings, mergedEq, by simp [traceEq]⟩

/-- Every instrumented row remains replayable before an arbitrary suffix.
This is the composition invariant for nested matching sites. -/
def ReplayRowsValid (replay : List Nat → Option (Bindings × List Nat))
    (rows : List (Bindings × List Nat)) : Prop :=
  ∀ row ∈ rows, ∀ suffix, replay (row.2 ++ suffix) = some (row.1, suffix)

theorem mergeGuidedRows_valid
    (first next : List Nat → Option (Bindings × List Nat))
    (heads tails : List (Bindings × List Nat))
    (headValid : ReplayRowsValid first heads) (tailValid : ReplayRowsValid next tails) :
    ReplayRowsValid (fun trace => joinReplay (first trace) next) (mergeGuidedRows heads tails) := by
  intro row member suffix
  obtain ⟨head, headMember, tail, tailMember, merged, traceEq⟩ :=
    (mem_mergeGuidedRows heads tails row).mp member
  simp only [traceEq, List.append_assoc]
  rw [headValid head headMember, joinReplay, tailValid tail tailMember]
  simp only [merged, Option.map_some]

private theorem enumerateArguments_valid_of (patterns targets : List Pattern)
    (pointwise : ∀ pattern ∈ patterns, ∀ target,
      ReplayRowsValid (replayPattern pattern target) (enumeratePattern pattern target)) :
    ReplayRowsValid (replayArguments patterns targets) (enumerateArguments patterns targets) := by
  induction patterns generalizing targets with
  | nil =>
      cases targets <;> simp [ReplayRowsValid, enumerateArguments, replayArguments]
  | cons pattern patterns ih =>
      cases targets with
      | nil => simp [ReplayRowsValid, enumerateArguments]
      | cons target targets =>
          have head := pointwise pattern (by simp) target
          have tail := ih targets (fun child member => pointwise child (by simp [member]))
          simpa only [ReplayRowsValid, enumerateArguments, replayArguments] using
            mergeGuidedRows_valid (replayPattern pattern target) (replayArguments patterns targets)
              (enumeratePattern pattern target) (enumerateArguments patterns targets) head tail

private theorem enumerateBag_valid_of (patterns : List Pattern) (rest : Option String)
    (kind : CollType) (targets : List Pattern)
    (pointwise : ∀ pattern ∈ patterns, ∀ target,
      ReplayRowsValid (replayPattern pattern target) (enumeratePattern pattern target)) :
    ReplayRowsValid (replayBag patterns rest kind targets) (enumerateBag patterns rest kind targets) := by
  induction patterns generalizing targets with
  | nil => cases rest <;> cases targets <;> simp [ReplayRowsValid, enumerateBag, replayBag]
  | cons pattern patterns ih =>
      intro row member suffix
      simp only [enumerateBag, List.mem_flatMap, List.mem_map] at member
      obtain ⟨⟨target, index⟩, selected, mergedRow, mergedMember, returned⟩ := member
      subst returned
      have lookup := List.mem_zipIdx_iff_getElem?.mp selected
      have head := pointwise pattern (by simp) target
      have tail := ih (targets.eraseIdx index) (fun child present => pointwise child (by simp [present]))
      have replayed := mergeGuidedRows_valid (replayPattern pattern target)
        (replayBag patterns rest kind (targets.eraseIdx index))
        (enumeratePattern pattern target) (enumerateBag patterns rest kind (targets.eraseIdx index))
        head tail mergedRow mergedMember suffix
      simpa only [List.cons_append, replayBag, lookup] using replayed

theorem enumeratePattern_valid (pattern target : Pattern) :
    ReplayRowsValid (replayPattern pattern target) (enumeratePattern pattern target) := by
  induction pattern using Pattern.inductionOn generalizing target with
  | hbvar index =>
      cases target with
      | bvar actual =>
          by_cases same : index = actual <;>
            simp [same, ReplayRowsValid, enumeratePattern, replayPattern]
      | _ => simp [ReplayRowsValid, enumeratePattern.eq_def]
  | hfvar name => simp [ReplayRowsValid, enumeratePattern, replayPattern]
  | happly label patterns ih =>
      have arguments := fun targets => enumerateArguments_valid_of patterns targets ih
      cases target with
      | apply actual targets =>
          by_cases admitted : label = actual ∧ patterns.length = targets.length
          · simpa [ReplayRowsValid, enumeratePattern, replayPattern, admitted.1, admitted.2] using arguments targets
          · simp [ReplayRowsValid, enumeratePattern, admitted]
      | _ => simp [ReplayRowsValid, enumeratePattern.eq_def]
  | hlambda display body ih =>
      cases target with
      | lambda actualDisplay actual =>
          simpa [ReplayRowsValid, enumeratePattern, replayPattern] using ih actual
      | _ => simp [ReplayRowsValid, enumeratePattern.eq_def]
  | hmultiLambda arity displays body ih =>
      cases target with
      | multiLambda actualArity actualDisplays actual =>
          by_cases same : arity = actualArity
          · simpa [ReplayRowsValid, enumeratePattern, replayPattern, same] using ih actual
          · simp [ReplayRowsValid, enumeratePattern, same]
      | _ => simp [ReplayRowsValid, enumeratePattern.eq_def]
  | hsubst body replacement ihBody ihReplacement =>
      cases target with
      | subst actualBody actualReplacement =>
          simpa only [ReplayRowsValid, enumeratePattern, replayPattern] using
            mergeGuidedRows_valid (replayPattern body actualBody) (replayPattern replacement actualReplacement)
              (enumeratePattern body actualBody) (enumeratePattern replacement actualReplacement)
              (ihBody actualBody) (ihReplacement actualReplacement)
      | _ => simp [ReplayRowsValid, enumeratePattern.eq_def]
  | hcollection kind patterns rest ih =>
      have arguments := fun targets => enumerateArguments_valid_of patterns targets ih
      have bag := fun targets => enumerateBag_valid_of patterns rest kind targets ih
      cases target with
      | collection actualKind targets actualRest =>
          by_cases same : kind = actualKind
          · subst actualKind
            by_cases vector : kind = .vec
            · subst kind
              cases rest with
              | none => simpa [ReplayRowsValid, enumeratePattern, replayPattern] using arguments targets
              | some name =>
                  have fixedValid : ReplayRowsValid
                      (fun trace => some ([(name, .collection .vec (targets.drop patterns.length) none)], trace))
                      [([(name, .collection .vec (targets.drop patterns.length) none)], [])] := by
                    simp [ReplayRowsValid]
                  simpa [ReplayRowsValid, enumeratePattern, replayPattern] using
                    mergeGuidedRows_valid (replayArguments patterns (targets.take patterns.length)) _
                      (enumerateArguments patterns (targets.take patterns.length)) _
                      (arguments (targets.take patterns.length)) fixedValid
            · simpa [ReplayRowsValid, enumeratePattern.eq_def, replayPattern.eq_def, vector] using bag targets
          · simp [ReplayRowsValid, enumeratePattern.eq_def, same]
      | _ => simp [ReplayRowsValid, enumeratePattern.eq_def]

theorem enumeratePattern_rows_accepted (pattern target : Pattern) (row : Bindings × List Nat)
    (member : row ∈ enumeratePattern pattern target) :
    checkGuidedMatch pattern target row.1 row.2 = true := by
  simp only [checkGuidedMatch, decide_eq_true_eq]
  simpa only [List.append_nil] using enumeratePattern_valid pattern target row member []

/-- Guidance annotates original result occurrences without creating or
removing answers. This is a list comparison internal to the matcher, not a
promise about a language-level answer order. -/
theorem enumeratePattern_length (pattern target : Pattern) :
    (enumeratePattern pattern target).length = (matchPattern pattern target).length := by
  simpa only [List.length_map] using congrArg List.length (enumeratePattern_project pattern target)

/-- Counting a binding after forgetting its choices agrees exactly with the
original matcher, including equal answers from different target occurrences. -/
theorem enumeratePattern_count (pattern target : Pattern) (bindings : Bindings) :
    (enumeratePattern pattern target).countP (fun row => row.1 == bindings) =
      (matchPattern pattern target).count bindings := by
  simpa only [List.count_eq_countP, List.countP_map, Function.comp_def] using
    congrArg (List.count bindings) (enumeratePattern_project pattern target)

private theorem enumeratePattern_collection_unordered (kind : CollType)
    (patterns targets : List Pattern) (rest actualRest : Option String) (notVector : kind ≠ .vec) :
    enumeratePattern (.collection kind patterns rest) (.collection kind targets actualRest) =
      enumerateBag patterns rest kind targets := by
  rw [enumeratePattern.eq_def]
  simp [notVector]

mutual

/-- Every guided source derivation corresponds to an actual instrumented
branch. The consumed prefix is independent of the unconsumed suffix. -/
theorem GuidedMatchRel.enumerated {pattern target : Pattern} {bindings : Bindings}
    {trace remaining : List Nat} (matched : GuidedMatchRel pattern target bindings trace remaining) :
    ∃ prefixWord, trace = prefixWord ++ remaining ∧ (bindings, prefixWord) ∈ enumeratePattern pattern target := by
  cases matched with
  | fvar => exact ⟨[], rfl, by simp [enumeratePattern]⟩
  | bvar => exact ⟨[], rfl, by simp [enumeratePattern]⟩
  | apply arguments sameLength =>
      obtain ⟨prefixWord, shape, member⟩ := arguments.enumerated
      exact ⟨prefixWord, shape, by simpa [enumeratePattern, sameLength] using member⟩
  | lambda body =>
      obtain ⟨prefixWord, shape, member⟩ := body.enumerated
      exact ⟨prefixWord, shape, by simpa only [enumeratePattern] using member⟩
  | multiLambda body =>
      obtain ⟨prefixWord, shape, member⟩ := body.enumerated
      exact ⟨prefixWord, shape, by simpa [enumeratePattern] using member⟩
  | collection notVector elements =>
      obtain ⟨prefixWord, shape, member⟩ := elements.enumerated
      refine ⟨prefixWord, shape, ?_⟩
      rw [enumeratePattern_collection_unordered _ _ _ _ _ notVector]
      exact member
  | vector arguments =>
      obtain ⟨prefixWord, shape, member⟩ := arguments.enumerated
      exact ⟨prefixWord, shape, by simpa [enumeratePattern] using member⟩
  | vectorRest prefixMatched merged =>
      obtain ⟨prefixWord, shape, member⟩ := prefixMatched.enumerated
      refine ⟨prefixWord, shape, ?_⟩
      simp only [enumeratePattern, beq_self_eq_true, ↓reduceIte]
      apply (mem_mergeGuidedRows _ _ _).mpr
      exact ⟨(_, prefixWord), member, (_, []), by simp, merged, by simp⟩
  | subst body replacement merged =>
      obtain ⟨bodyWord, bodyShape, bodyMember⟩ := body.enumerated
      obtain ⟨replacementWord, replacementShape, replacementMember⟩ := replacement.enumerated
      refine ⟨bodyWord ++ replacementWord, ?_, ?_⟩
      · simp only [bodyShape, replacementShape, List.append_assoc]
      · simp only [enumeratePattern]
        exact (mem_mergeGuidedRows _ _ _).mpr
          ⟨(_, bodyWord), bodyMember, (_, replacementWord), replacementMember, merged, rfl⟩

theorem GuidedArgumentsRel.enumerated {patterns targets : List Pattern} {bindings : Bindings}
    {trace remaining : List Nat} (matched : GuidedArgumentsRel patterns targets bindings trace remaining) :
    ∃ prefixWord, trace = prefixWord ++ remaining ∧ (bindings, prefixWord) ∈ enumerateArguments patterns targets := by
  cases matched with
  | nil => exact ⟨[], rfl, by simp [enumerateArguments]⟩
  | cons head tail merged =>
      obtain ⟨headWord, headShape, headMember⟩ := head.enumerated
      obtain ⟨tailWord, tailShape, tailMember⟩ := tail.enumerated
      refine ⟨headWord ++ tailWord, ?_, ?_⟩
      · simp only [headShape, tailShape, List.append_assoc]
      · simp only [enumerateArguments]
        exact (mem_mergeGuidedRows _ _ _).mpr
          ⟨(_, headWord), headMember, (_, tailWord), tailMember, merged, rfl⟩

theorem GuidedBagRel.enumerated {patterns targets : List Pattern} {rest : Option String}
    {kind : CollType} {bindings : Bindings} {trace remaining : List Nat}
    (matched : GuidedBagRel patterns rest kind targets bindings trace remaining) :
    ∃ prefixWord, trace = prefixWord ++ remaining ∧ (bindings, prefixWord) ∈ enumerateBag patterns rest kind targets := by
  cases matched with
  | nilNoRest => exact ⟨[], rfl, by simp [enumerateBag]⟩
  | nilRest => exact ⟨[], rfl, by simp [enumerateBag]⟩
  | cons index within head tail merged =>
      obtain ⟨headWord, headShape, headMember⟩ := head.enumerated
      obtain ⟨tailWord, tailShape, tailMember⟩ := tail.enumerated
      refine ⟨index :: (headWord ++ tailWord), ?_, ?_⟩
      · simp only [List.cons_append, headShape, tailShape, List.append_assoc]
      · simp only [enumerateBag, List.mem_flatMap, List.mem_map]
        refine ⟨(targets[index], index), ?_, (bindings, headWord ++ tailWord), ?_, rfl⟩
        · exact List.mem_zipIdx_iff_getElem?.mpr (by simp [within])
        · exact (mem_mergeGuidedRows _ _ _).mpr
            ⟨(_, headWord), headMember, (_, tailWord), tailMember, merged, rfl⟩

end

theorem mem_enumeratePattern_iff_accepted (pattern target : Pattern) (row : Bindings × List Nat) :
    row ∈ enumeratePattern pattern target ↔ checkGuidedMatch pattern target row.1 row.2 = true := by
  rcases row with ⟨bindings, trace⟩
  constructor
  · exact enumeratePattern_rows_accepted pattern target (bindings, trace)
  · intro accepted
    obtain ⟨prefixWord, shape, member⟩ :=
      ((checkGuidedMatch_exact pattern target bindings trace).mp accepted).enumerated
    have same : trace = prefixWord := by simpa using shape
    simpa only [same] using member

namespace GuidedControls

theorem annotated_duplicate_occurrences :
    enumeratePattern pairPattern duplicateTarget =
      [(duplicateBindings, [0, 0]), (duplicateBindings, [1, 0])] := by decide +kernel

theorem annotated_duplicate_count :
    (enumeratePattern pairPattern duplicateTarget).countP
      (fun row => row.1 == duplicateBindings) = 2 := by decide +kernel

theorem duplicate_choices_remain_distinct :
    (enumeratePattern pairPattern duplicateTarget).Nodup := by decide +kernel

theorem impossible_matching_has_no_annotation :
    enumeratePattern (.apply "Pair" [.fvar "x", .fvar "x"])
      (.apply "Pair" [atomA, atomB]) = [] := by decide +kernel

end GuidedControls


/-! ## Unique matching occurrences -/

private theorem filterMap_nodup_on {α β : Type} (rows : List α) (f : α → Option β)
    (distinct : rows.Nodup)
    (unique : ∀ first ∈ rows, ∀ second ∈ rows, ∀ value,
      f first = some value → f second = some value → first = second) :
    (rows.filterMap f).Nodup := by
  apply List.Pairwise.filterMap f ?_ ((List.Pairwise.and_mem).mp distinct)
  intro first second ⟨firstMember, secondMember, different⟩ value firstEq value' secondEq same
  apply different
  apply unique first firstMember second secondMember value firstEq
  simpa only [same] using secondEq

/-- A deterministic prefix parser distinguishes complete rows by their
choice words, even if their mathematical binding results are equal. -/
theorem ReplayRowsValid.choice_injective
    {replay : List Nat → Option (Bindings × List Nat)} {rows : List (Bindings × List Nat)}
    (valid : ReplayRowsValid replay rows)
    {first second : Bindings × List Nat} (firstMember : first ∈ rows)
    (secondMember : second ∈ rows) (same : first.2 = second.2) : first = second := by
  have firstRead := valid first firstMember []
  have secondRead := valid second secondMember []
  rw [same] at firstRead
  have sameBinding : first.1 = second.1 := by
    have := firstRead.symm.trans secondRead
    simpa only [Option.some.injEq, Prod.mk.injEq, and_true] using this
  exact Prod.ext sameBinding same

private theorem choice_split_unique
    (firstReplay nextReplay : List Nat → Option (Bindings × List Nat))
    (heads tails : List (Bindings × List Nat))
    (headValid : ReplayRowsValid firstReplay heads) (tailValid : ReplayRowsValid nextReplay tails)
    {firstHead secondHead firstTail secondTail : Bindings × List Nat}
    (firstHeadMember : firstHead ∈ heads) (secondHeadMember : secondHead ∈ heads)
    (firstTailMember : firstTail ∈ tails) (secondTailMember : secondTail ∈ tails)
    (same : firstHead.2 ++ firstTail.2 = secondHead.2 ++ secondTail.2) :
    firstHead = secondHead ∧ firstTail = secondTail := by
  have firstRead := headValid firstHead firstHeadMember firstTail.2
  have secondRead := headValid secondHead secondHeadMember secondTail.2
  rw [same] at firstRead
  have split : firstHead.1 = secondHead.1 ∧ firstTail.2 = secondTail.2 := by
    simpa only [Option.some.injEq, Prod.mk.injEq] using firstRead.symm.trans secondRead
  have sameHeadWord : firstHead.2 = secondHead.2 := by
    rw [split.2] at same
    exact List.append_cancel_right same
  exact ⟨Prod.ext split.1 sameHeadWord,
    tailValid.choice_injective firstTailMember secondTailMember split.2⟩

/-- Composing independent guided prefix parsers does not identify distinct
producer occurrences, even when binding merges forget their provenance. -/
theorem mergeGuidedRows_nodup
    (firstReplay nextReplay : List Nat → Option (Bindings × List Nat))
    (heads tails : List (Bindings × List Nat))
    (headValid : ReplayRowsValid firstReplay heads) (tailValid : ReplayRowsValid nextReplay tails)
    (headDistinct : heads.Nodup) (tailDistinct : tails.Nodup) :
    (mergeGuidedRows heads tails).Nodup := by
  let mergeRow := fun (pair : (Bindings × List Nat) × (Bindings × List Nat)) =>
    (mergeBindings pair.1.1 pair.2.1).map
      (fun bindings => (bindings, pair.1.2 ++ pair.2.2))
  have shape : mergeGuidedRows heads tails = (heads ×ˢ tails).filterMap mergeRow := by
    simp [mergeGuidedRows, SProd.sprod, List.product, List.filterMap_flatMap,
      List.filterMap_map, mergeRow]
  rw [shape]
  apply filterMap_nodup_on _ _ (headDistinct.product tailDistinct)
  intro first firstMember second secondMember row firstEq secondEq
  obtain ⟨firstHeadMember, firstTailMember⟩ := List.mem_product.mp firstMember
  obtain ⟨secondHeadMember, secondTailMember⟩ := List.mem_product.mp secondMember
  obtain ⟨firstBindings, _firstMerge, firstResult⟩ := Option.map_eq_some_iff.mp firstEq
  obtain ⟨secondBindings, _secondMerge, secondResult⟩ := Option.map_eq_some_iff.mp secondEq
  have sameWord : first.1.2 ++ first.2.2 = second.1.2 ++ second.2.2 :=
    congrArg Prod.snd (firstResult.trans secondResult.symm)
  obtain ⟨sameHead, sameTail⟩ := choice_split_unique firstReplay nextReplay heads tails
    headValid tailValid firstHeadMember secondHeadMember firstTailMember secondTailMember sameWord
  exact Prod.ext sameHead sameTail


theorem enumerateArguments_valid (patterns targets : List Pattern) :
    ReplayRowsValid (replayArguments patterns targets) (enumerateArguments patterns targets) :=
  enumerateArguments_valid_of patterns targets (fun pattern _member target => enumeratePattern_valid pattern target)

theorem enumerateBag_valid (patterns : List Pattern) (rest : Option String)
    (kind : CollType) (targets : List Pattern) :
    ReplayRowsValid (replayBag patterns rest kind targets) (enumerateBag patterns rest kind targets) :=
  enumerateBag_valid_of patterns rest kind targets (fun pattern _member target => enumeratePattern_valid pattern target)

private theorem enumerateArguments_nodup_of (patterns targets : List Pattern)
    (pointwise : ∀ pattern ∈ patterns, ∀ target, (enumeratePattern pattern target).Nodup) :
    (enumerateArguments patterns targets).Nodup := by
  induction patterns generalizing targets with
  | nil => cases targets <;> simp [enumerateArguments]
  | cons pattern patterns ih =>
      cases targets with
      | nil => simp [enumerateArguments]
      | cons target targets =>
          simpa only [enumerateArguments] using
            mergeGuidedRows_nodup (replayPattern pattern target) (replayArguments patterns targets)
            (enumeratePattern pattern target) (enumerateArguments patterns targets)
            (enumeratePattern_valid pattern target) (enumerateArguments_valid patterns targets)
            (pointwise pattern (by simp) target)
            (ih targets (fun child member => pointwise child (by simp [member])))

private theorem enumerateBag_nodup_of (patterns : List Pattern) (rest : Option String)
    (kind : CollType) (targets : List Pattern)
    (pointwise : ∀ pattern ∈ patterns, ∀ target, (enumeratePattern pattern target).Nodup) :
    (enumerateBag patterns rest kind targets).Nodup := by
  induction patterns generalizing targets with
  | nil => cases rest <;> cases targets <;> simp [enumerateBag]
  | cons pattern patterns ih =>
      simp only [enumerateBag]
      apply List.nodup_flatMap.mpr
      constructor
      · intro pair _member
        have joined := mergeGuidedRows_nodup (replayPattern pattern pair.1)
            (replayBag patterns rest kind (targets.eraseIdx pair.2))
            (enumeratePattern pattern pair.1) (enumerateBag patterns rest kind (targets.eraseIdx pair.2))
            (enumeratePattern_valid pattern pair.1) (enumerateBag_valid patterns rest kind (targets.eraseIdx pair.2))
            (pointwise pattern (by simp) pair.1)
            (ih (targets.eraseIdx pair.2) (fun child member => pointwise child (by simp [member])))
        exact joined.map (f := fun row : Bindings × List Nat => (row.1, pair.2 :: row.2))
          fun first second same => by
            cases first
            cases second
            simpa only [Prod.mk.injEq, List.cons.injEq, true_and] using same
      · have indices : (targets.zipIdx.map Prod.snd).Nodup := by
          rw [List.zipIdx_map_snd]
          exact List.nodup_range'
        have distinctIndices := List.pairwise_map.mp indices
        apply distinctIndices.imp
        intro first second distinct row firstMember secondMember
        obtain ⟨firstRow, _firstMember, firstShape⟩ := List.mem_map.mp firstMember
        obtain ⟨secondRow, _secondMember, secondShape⟩ := List.mem_map.mp secondMember
        apply distinct
        exact (List.cons.inj (congrArg Prod.snd (firstShape.trans secondShape.symm))).1

/-- Distinct branches of the original matcher have distinct guided rows;
equal binding values therefore retain separate evidence occurrences. -/
theorem enumeratePattern_nodup (pattern target : Pattern) :
    (enumeratePattern pattern target).Nodup := by
  induction pattern using Pattern.inductionOn generalizing target with
  | hbvar index =>
      cases target with
      | bvar actual =>
          by_cases same : index = actual <;> simp [enumeratePattern, same]
      | _ => simp [enumeratePattern.eq_def]
  | hfvar name => simp [enumeratePattern]
  | happly label patterns ih =>
      have arguments := fun targets => enumerateArguments_nodup_of patterns targets ih
      cases target with
      | apply actual targets =>
          by_cases admitted : label = actual ∧ patterns.length = targets.length
          · simpa [enumeratePattern, admitted.1, admitted.2] using arguments targets
          · simp [enumeratePattern, admitted]
      | _ => simp [enumeratePattern.eq_def]
  | hlambda display body ih =>
      cases target with
      | lambda actualDisplay actual => simpa only [enumeratePattern] using ih actual
      | _ => simp [enumeratePattern.eq_def]
  | hmultiLambda arity displays body ih =>
      cases target with
      | multiLambda actualArity actualDisplays actual =>
          by_cases same : arity = actualArity
          · simpa [enumeratePattern, same] using ih actual
          · simp [enumeratePattern, same]
      | _ => simp [enumeratePattern.eq_def]
  | hsubst body replacement ihBody ihReplacement =>
      cases target with
      | subst actualBody actualReplacement =>
          simpa only [enumeratePattern] using
            mergeGuidedRows_nodup (replayPattern body actualBody) (replayPattern replacement actualReplacement)
            (enumeratePattern body actualBody) (enumeratePattern replacement actualReplacement)
            (enumeratePattern_valid body actualBody) (enumeratePattern_valid replacement actualReplacement)
            (ihBody actualBody) (ihReplacement actualReplacement)
      | _ => simp [enumeratePattern.eq_def]
  | hcollection kind patterns rest ih =>
      have arguments := fun targets => enumerateArguments_nodup_of patterns targets ih
      have bag := fun targets => enumerateBag_nodup_of patterns rest kind targets ih
      cases target with
      | collection actualKind targets actualRest =>
          by_cases same : kind = actualKind
          · subst actualKind
            by_cases vector : kind = .vec
            · subst kind
              cases rest with
              | none => simpa [enumeratePattern] using arguments targets
              | some name =>
                  have fixedValid : ReplayRowsValid
                      (fun trace => some ([(name, .collection .vec (targets.drop patterns.length) none)], trace))
                      [([(name, .collection .vec (targets.drop patterns.length) none)], [])] := by
                    simp [ReplayRowsValid]
                  simpa [enumeratePattern] using mergeGuidedRows_nodup
                    (replayArguments patterns (targets.take patterns.length)) _
                    (enumerateArguments patterns (targets.take patterns.length)) _
                    (enumerateArguments_valid patterns (targets.take patterns.length)) fixedValid
                    (arguments (targets.take patterns.length)) (by simp)
            · simpa [enumeratePattern.eq_def, vector] using bag targets
          · simp [enumeratePattern.eq_def, same]
      | _ => simp [enumeratePattern.eq_def]

/-- A complete choice word identifies exactly one matching occurrence. -/
theorem enumeratePattern_choices_nodup (pattern target : Pattern) :
    ((enumeratePattern pattern target).map Prod.snd).Nodup :=
  (enumeratePattern_nodup pattern target).map_on fun _ firstMember _ secondMember same =>
    (enumeratePattern_valid pattern target).choice_injective firstMember secondMember same

end Mettapedia.OSLF.MeTTaIL.MatchEvidence
