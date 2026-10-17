import Mettapedia.TypeTheory.BubbleJoinCongruence
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.MeTTaIL.LinearMatch

/-!
# The contextual engine is the congruence closure of the bubble

The contextual engine of a language definition steps at the root only; it
reaches inside a term through authored congruence rows.  A **congruence row**
for one argument position of a constructor rewrites `c(…, x, …)` to
`c(…, y, …)` when `x` steps to `y`, with distinct metavariables at the other
positions (`IsCongruenceRow`).  A language is **row-presented** when each of
its rows is either premise-free or a congruence row (`RowPresented`).

* For a row-presented language the engine's least relation is exactly the
  bubble of its premise-free rows, applied at the hole of a context whose
  frames all carry congruence rows (`step_iff_rowStep`).  The ordered results
  at some fuel are the same relation (`rewriteAt_iff_rowStep`), and so is
  conversion (`eqvGen_step_eq_rowStep`).
* **All positions.**  On a term whose every application carries congruence
  rows at every argument position (`RowCovered`), the engine's steps are the
  steps of the congruence closure of the bubble (`step_iff_patternStep`).
  The ordered-results statements about the engine and the conversion and
  normal-form statements about bubbles therefore speak about one relation.

Controls: a language with rows at both positions of a pair steps inside it;
without the rows the congruence closure steps where the engine does not; a
non-linear congruence row steps where no row context reaches.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleJoinEngine

open Relation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.LinearMatch
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.TypeTheory.BubbleJoinCongruence

/-! ## Congruence rows and row contexts -/

/-- A **congruence row** for one argument position of a constructor: from
`c(…, x, …)` to `c(…, y, …)` when `x` steps to `y`, with distinct metavariables
at the other positions. -/
def IsCongruenceRow (rule : RewriteRule) (constructor : String)
    (beforeCount afterCount : Nat) : Prop :=
  ∃ (before after : List String) (source target : String),
    before.length = beforeCount ∧ after.length = afterCount ∧
      (before ++ source :: after).Nodup ∧ target ∉ before ++ source :: after ∧
      rule.premises = [.congruence (.fvar source) (.fvar target)] ∧
      rule.left = .apply constructor ((before ++ source :: after).map .fvar) ∧
      rule.right = .apply constructor ((before ++ target :: after).map .fvar)

/-- A language whose rows are premise-free root rows or congruence rows. -/
def RowPresented (language : LanguageDef) : Prop :=
  ∀ rule ∈ language.rewrites, rule.premises = [] ∨
    ∃ constructor beforeCount afterCount,
      IsCongruenceRow rule constructor beforeCount afterCount

/-- Contexts whose every frame is an argument position carrying a congruence
row of the language. -/
inductive RowContext (language : LanguageDef) : OneHoleContext → Prop where
  | hole : RowContext language .hole
  | frame {constructor : String} {before after : List Pattern} {inner : OneHoleContext}
      (rule : RewriteRule) (member : rule ∈ language.rewrites)
      (row : IsCongruenceRow rule constructor before.length after.length) :
      RowContext language inner → RowContext language (.apply constructor before inner after)

/-- Root steps of the language's bubble at the holes of row contexts. -/
def RowStep (language : LanguageDef) (source target : Pattern) : Prop :=
  ∃ context redex contractum, RowContext language context ∧
    languageBubble language redex contractum ∧
      context.fill redex = source ∧ context.fill contractum = target

/-! ## Matching a congruence row -/

private theorem binderFreeList_fvars (names : List String) :
    binderFreeList (names.map Pattern.fvar) = true := by
  induction names with
  | nil => simp [binderFreeList]
  | cons name names inductionHypothesis =>
      simp [binderFreeList, binderFree, inductionHypothesis]

/-- A congruence row fires by syntactic substitution. -/
private theorem applyRow {rule : RewriteRule} {constructor : String}
    {before after : List String} {source target : String}
    (left : rule.left = .apply constructor ((before ++ source :: after).map .fvar))
    (right : rule.right = .apply constructor ((before ++ target :: after).map .fvar))
    (language : LanguageDef) (bindings : Bindings) :
    applyBindingsForRule language rule bindings =
      .apply constructor (((before ++ target :: after).map .fvar).map
        (applyBindings bindings)) := by
  have aligned : ruleDepthAligned rule = true := by
    apply ruleDepthAligned_of_binderFree
    · rw [left]
      exact binderFreeList_fvars _
    · rw [right]
      exact binderFreeList_fvars _
  rw [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings rule bindings aligned,
    right]
  simp [applyBindings]

/-- A list as long as `before ++ middle :: after` splits at the same place. -/
private theorem split_like {α β : Type} (before : List α) (middle : α) (after : List α)
    (terms : List β) (lengths : (before ++ middle :: after).length = terms.length) :
    ∃ beforeTerms middleTerm afterTerms,
      terms = beforeTerms ++ middleTerm :: afterTerms ∧
        beforeTerms.length = before.length ∧ afterTerms.length = after.length := by
  induction before generalizing terms with
  | nil =>
      cases terms with
      | nil => simp at lengths
      | cons first rest =>
          refine ⟨[], first, rest, rfl, rfl, ?_⟩
          simp at lengths
          omega
  | cons head tail inductionHypothesis =>
      cases terms with
      | nil => simp at lengths
      | cons first rest =>
          obtain ⟨beforeTerms, middleTerm, afterTerms, rfl, beforeLength, afterLength⟩ :=
            inductionHypothesis rest (by simpa using lengths)
          exact ⟨first :: beforeTerms, middleTerm, afterTerms, rfl, by simp [beforeLength],
            afterLength⟩

/-- Zipping two lists split at the same place. -/
private theorem zip_split {α β : Type} (before after : List α) (middle : α)
    (beforeTerms afterTerms : List β) (middleTerm : β)
    (beforeLength : beforeTerms.length = before.length) :
    (before ++ middle :: after).zip (beforeTerms ++ middleTerm :: afterTerms) =
      before.zip beforeTerms ++ (middle, middleTerm) :: after.zip afterTerms := by
  rw [List.zip_append beforeLength.symm, List.zip_cons_cons]

/-- Applying the bindings of a congruence step to the row's right side. -/
private theorem applyRight {bindings : Bindings} {before after : List String}
    {source target : String} {beforeTerms afterTerms : List Pattern}
    {sourceTerm targetTerm : Pattern} (fresh : target ∉ before ++ source :: after)
    (beforeLength : beforeTerms.length = before.length)
    (afterLength : afterTerms.length = after.length)
    (namesOnly : ∀ pair ∈ bindings, pair.1 ∈ before ++ source :: after)
    (bindingsNodup : (bindings.map Prod.fst).Nodup)
    (pairs : ∀ pair ∈ (before ++ source :: after).zip (beforeTerms ++ sourceTerm :: afterTerms),
      pair ∈ bindings) :
    ((before ++ target :: after).map Pattern.fvar).map
        (applyBindings ((target, targetTerm) :: bindings)) =
      beforeTerms ++ targetTerm :: afterTerms := by
  apply applyBindings_fvars
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, bindingsNodup⟩
    intro member
    obtain ⟨pair, pairMember, pairName⟩ := List.mem_map.mp member
    exact fresh (pairName ▸ namesOnly pair pairMember)
  · simp [beforeLength, afterLength]
  · intro pair member
    rw [zip_split before after target beforeTerms afterTerms targetTerm beforeLength] at member
    rw [zip_split before after source beforeTerms afterTerms sourceTerm beforeLength] at pairs
    rcases List.mem_append.mp member with inBefore | inRest
    · exact List.mem_cons_of_mem _ (pairs pair (List.mem_append_left _ inBefore))
    · rcases List.mem_cons.mp inRest with rfl | inAfter
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _
          (pairs pair (List.mem_append_right _ (List.mem_cons_of_mem _ inAfter)))

/-! ## The engine is the row closure of the bubble -/

/-- A premise-free root step of the bubble is a step of the engine. -/
private theorem step_of_bubble {base : BasePremiseEvaluator} {language : LanguageDef}
    {redex contractum : Pattern} (bubble : languageBubble language redex contractum) :
    Step base language redex contractum := by
  simp only [languageBubble, rewriteStep, List.mem_flatMap] at bubble
  obtain ⟨rule, member, applied⟩ := bubble
  unfold applyRule at applied
  split at applied
  · rename_i premiseFree
    obtain ⟨initial, matched, rfl⟩ := List.mem_map.mp applied
    have noPremises : rule.premises = [] := List.isEmpty_iff.mp premiseFree
    refine ⟨1, .rule member (by rw [matchPatternForRule_eq_syntactic]; exact matched) ?_
      (applyBindingsForRule_eq_syntactic language rule initial)⟩
    rw [noPremises]
    exact .nil initial
  · simp at applied

/-- **Every row step is a step of the engine.** -/
theorem step_of_rowStep {base : BasePremiseEvaluator} {language : LanguageDef}
    {source target : Pattern} (stepped : RowStep language source target) :
    Step base language source target := by
  obtain ⟨context, redex, contractum, rowContext, bubble, rfl, rfl⟩ := stepped
  induction rowContext with
  | hole => exact step_of_bubble bubble
  | @frame constructor beforeTerms afterTerms inner rule member row _ inductionHypothesis =>
      obtain ⟨before, after, source, target, beforeLength, afterLength, nodup, fresh,
        premisesEq, left, right⟩ := row
      obtain ⟨initial, matched, initialNodup, initialNames, pairs⟩ :=
        matchArgs_fvars (before ++ source :: after)
          (beforeTerms ++ inner.fill redex :: afterTerms) nodup
          (by simp [beforeLength, afterLength])
      have sourcePair : (source, inner.fill redex) ∈ initial := by
        apply pairs
        rw [zip_split before after source beforeTerms afterTerms _ beforeLength.symm]
        simp
      have lookupSource : applyBindings initial (.fvar source) = inner.fill redex := by
        simp [applyBindings, find?_of_mem_of_nodup initial initialNodup sourcePair]
      have targetFresh : ∀ name ∈ [(target, inner.fill contractum)].map Prod.fst,
          name ∉ initial.map Prod.fst := by
        intro name member inInitial
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
        subst member
        exact fresh ((initialNames name).mp inInitial)
      have merged := mergeBindings_of_fresh [(target, inner.fill contractum)] initial
        targetFresh (by simp)
      apply step_of_single_congruence_rule member
        (initialBindings := initial) (finalBindings := (target, inner.fill contractum) :: initial)
        (premiseBindings := [(target, inner.fill contractum)])
        (candidate := inner.fill contractum)
      · rw [matchPatternForRule_eq_syntactic, left]
        simp only [OneHoleContext.fill, matchPattern]
        simpa [beforeLength, afterLength] using matched
      · exact premisesEq
      · rw [lookupSource]
        exact inductionHypothesis
      · simp [matchPattern]
      · simpa using merged
      · rw [applyRow left right]
        simp only [OneHoleContext.fill]
        congr 1
        apply applyRight fresh beforeLength.symm afterLength.symm _ initialNodup pairs
        intro pair pairMember
        exact (initialNames pair.1).mp (List.mem_map_of_mem pairMember)

/-- **Every step of the engine of a row-presented language is a row step.** -/
theorem rowStep_of_stepAt {base : BasePremiseEvaluator} {language : LanguageDef}
    (presented : RowPresented language) :
    ∀ fuel source target, StepAt base language fuel source target →
      RowStep language source target := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target stepped
      cases stepped
  | succ fuel inductionHypothesis =>
      intro source target stepped
      cases stepped with
      | @rule _ _ _ rule initial final member matched premises targetEq =>
          rw [matchPatternForRule_eq_syntactic] at matched
          rcases presented rule member with premiseFree | ⟨constructor, _, _, row⟩
          · rw [premiseFree] at premises
            cases premises
            refine ⟨.hole, source, target, .hole, ?_, rfl, rfl⟩
            simp only [languageBubble, rewriteStep, List.mem_flatMap]
            refine ⟨rule, member, ?_⟩
            simp only [applyRule, premiseFree, List.isEmpty_nil, if_true, List.mem_map]
            exact ⟨initial, matched, by rw [← targetEq, applyBindingsForRule_eq_syntactic]⟩
          · obtain ⟨before, after, sourceName, targetName, beforeLength, afterLength, nodup,
              fresh, premisesEq, left, right⟩ := row
            rw [left] at matched
            cases source with
            | apply sourceConstructor arguments =>
                simp only [matchPattern] at matched
                split at matched
                · rename_i shape
                  simp only [Bool.and_eq_true, beq_iff_eq, List.length_map] at shape
                  obtain ⟨rfl, lengths⟩ := shape
                  obtain ⟨namesOnly, initialNodup, pairs⟩ :=
                    matchArgsRel_fvars_inversion _ arguments initial
                      (matchArgs_iff_matchArgsRel.mp matched) nodup
                  obtain ⟨beforeTerms, sourceTerm, afterTerms, rfl, beforeTermsLength,
                    afterTermsLength⟩ := split_like before sourceName after arguments lengths
                  rw [premisesEq] at premises
                  cases premises with
                  | cons premise rest =>
                      cases rest
                      cases premise with
                      | @congruence _ _ premiseBindings _ _ _ candidate recursive
                          premiseMatched merged =>
                          simp only [matchPattern, List.mem_singleton] at premiseMatched
                          subst premiseMatched
                          have sourcePair : (sourceName, sourceTerm) ∈ initial := by
                            apply pairs
                            rw [zip_split before after sourceName beforeTerms afterTerms _
                              beforeTermsLength]
                            simp
                          have lookupSource :
                              applyBindings initial (.fvar sourceName) = sourceTerm := by
                            simp [applyBindings,
                              find?_of_mem_of_nodup initial initialNodup sourcePair]
                          rw [lookupSource] at recursive
                          have targetFresh :
                              ∀ name ∈ [(targetName, candidate)].map Prod.fst,
                                name ∉ initial.map Prod.fst := by
                            intro name member inInitial
                            simp only [List.map_cons, List.map_nil,
                              List.mem_singleton] at member
                            subst member
                            obtain ⟨pair, pairMember, pairName⟩ := List.mem_map.mp inInitial
                            exact fresh (pairName ▸ namesOnly pair pairMember)
                          rw [mergeBindings_of_fresh _ initial targetFresh (by simp)] at merged
                          simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
                            List.singleton_append, Option.some.injEq] at merged
                          subst merged
                          obtain ⟨innerContext, redex, contractum, innerRow, bubble,
                            fillRedex, fillContractum⟩ :=
                            inductionHypothesis _ _ recursive
                          refine ⟨.apply constructor beforeTerms innerContext afterTerms,
                            redex, contractum,
                            .frame rule member ⟨before, after, sourceName, targetName,
                              beforeTermsLength.symm ▸ rfl, afterTermsLength.symm ▸ rfl,
                              nodup, fresh, premisesEq, left, right⟩ innerRow,
                            bubble, ?_, ?_⟩
                          · simp [OneHoleContext.fill, fillRedex]
                          · rw [← targetEq, applyRow left right]
                            simp only [OneHoleContext.fill, fillContractum]
                            congr 1
                            exact (applyRight fresh beforeTermsLength afterTermsLength
                              namesOnly initialNodup pairs).symm
                · simp at matched
            | _ => simp [matchPattern] at matched

/-- **The engine of a row-presented language is the row closure of its
bubble.** -/
theorem step_iff_rowStep {base : BasePremiseEvaluator} {language : LanguageDef}
    (presented : RowPresented language) {source target : Pattern} :
    Step base language source target ↔ RowStep language source target :=
  ⟨fun ⟨fuel, stepped⟩ => rowStep_of_stepAt presented fuel source target stepped,
    step_of_rowStep⟩

/-- The engine's ordered results at some fuel are the row closure of the
bubble. -/
theorem rewriteAt_iff_rowStep {base : BasePremiseEvaluator} {language : LanguageDef}
    (presented : RowPresented language) {source target : Pattern} :
    (∃ fuel, target ∈ rewriteAt base language fuel source) ↔
      RowStep language source target :=
  exists_mem_rewriteAt_iff_step.trans (step_iff_rowStep presented)

/-- Conversion of the engine is conversion of the row closure. -/
theorem eqvGen_step_eq_rowStep {base : BasePremiseEvaluator} {language : LanguageDef}
    (presented : RowPresented language) :
    EqvGen (Step base language) = EqvGen (RowStep language) := by
  have same : Step base language = RowStep language :=
    funext fun _ => funext fun _ => propext (step_iff_rowStep presented)
  rw [same]

/-! ## All positions -/

/-- Every application of the term carries congruence rows at every argument
position; leaves are metavariables and bound variables. -/
inductive RowCovered (language : LanguageDef) : Pattern → Prop where
  | fvar (name : String) : RowCovered language (.fvar name)
  | bvar (index : Nat) : RowCovered language (.bvar index)
  | apply {constructor : String} {arguments : List Pattern}
      (rows : ∀ before inner after, arguments = before ++ inner :: after →
        ∃ rule ∈ language.rewrites,
          IsCongruenceRow rule constructor before.length after.length)
      (inside : ∀ argument ∈ arguments, RowCovered language argument) :
      RowCovered language (.apply constructor arguments)

/-- Every context of a covered term is a row context. -/
theorem rowContext_of_covered {language : LanguageDef} :
    ∀ (context : OneHoleContext) {pattern : Pattern},
      RowCovered language (context.fill pattern) → RowContext language context
  | .hole, _, _ => .hole
  | .apply constructor before inner after, pattern, covered => by
      change RowCovered language (.apply constructor (before ++ inner.fill pattern :: after))
        at covered
      cases covered with
      | apply rows inside =>
          obtain ⟨rule, member, row⟩ := rows before (inner.fill pattern) after rfl
          exact .frame rule member row
            (rowContext_of_covered inner (pattern := pattern)
              (inside (inner.fill pattern) (by simp)))
  | .lambda _ _, _, covered => by cases covered
  | .multiLambda _ _ _, _, covered => by cases covered
  | .substBody _ _, _, covered => by cases covered
  | .substReplacement _ _, _, covered => by cases covered
  | .collection _ _ _ _ _, _, covered => by cases covered

/-- **All positions: the engine is the congruence closure of the bubble.**  On
a term whose every application carries congruence rows at every argument
position, a step of the engine of a row-presented language is exactly a step
of the bubble at some position. -/
theorem step_iff_patternStep {base : BasePremiseEvaluator} {language : LanguageDef}
    (presented : RowPresented language) {source target : Pattern}
    (covered : RowCovered language source) :
    Step base language source target ↔
      patternClosure.step (languageBubble language) source target := by
  rw [step_iff_rowStep presented]
  constructor
  · rintro ⟨context, redex, contractum, _, bubble, fillRedex, fillContractum⟩
    exact ⟨context, redex, contractum, bubble, fillRedex, fillContractum⟩
  · rintro ⟨context, redex, contractum, bubble, fillRedex, fillContractum⟩
    exact ⟨context, redex, contractum, rowContext_of_covered context (fillRedex ▸ covered),
      bubble, fillRedex, fillContractum⟩

/-! ## Controls -/

/-- The root row `a ↦ b`. -/
def rootRow : RewriteRule :=
  { name := "ab", typeContext := [], premises := [], left := .apply "a" [],
    right := .apply "b" [] }

/-- The congruence row at the first position of a pair. -/
def leftRow : RewriteRule :=
  { name := "pairLeft", typeContext := [], premises := [.congruence (.fvar "x") (.fvar "y")],
    left := .apply "pair" [.fvar "x", .fvar "z"], right := .apply "pair" [.fvar "y", .fvar "z"] }

/-- The congruence row at the second position of a pair. -/
def rightRow : RewriteRule :=
  { name := "pairRight", typeContext := [], premises := [.congruence (.fvar "x") (.fvar "y")],
    left := .apply "pair" [.fvar "z", .fvar "x"], right := .apply "pair" [.fvar "z", .fvar "y"] }

/-- Constants `a`, `b` and pairs over one sort, with the given rows. -/
def pairs (rows : List RewriteRule) : LanguageDef where
  name := "pairs"
  types := [TypeDecl.plain "S"]
  terms := [{ label := "a", category := "S", params := [], syntaxPattern := [] },
    { label := "b", category := "S", params := [], syntaxPattern := [] },
    { label := "pair", category := "S",
      params := [.simple "l" (.base "S"), .simple "r" (.base "S")], syntaxPattern := [] }]
  equations := []
  rewrites := rows

/-- Rows at both positions of a pair. -/
abbrev pairLanguage : LanguageDef := pairs [rootRow, leftRow, rightRow]

theorem leftRow_row : IsCongruenceRow leftRow "pair" 0 1 :=
  ⟨[], ["z"], "x", "y", rfl, rfl, by decide, by decide, rfl, rfl, rfl⟩

theorem rightRow_row : IsCongruenceRow rightRow "pair" 1 0 :=
  ⟨["z"], [], "x", "y", rfl, rfl, by decide, by decide, rfl, rfl, rfl⟩

theorem pairLanguage_presented : RowPresented pairLanguage := by
  intro rule member
  simp only [pairs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨_, _, _, leftRow_row⟩
  · exact Or.inr ⟨_, _, _, rightRow_row⟩

private def aTerm : Pattern := .apply "a" []
private def bTerm : Pattern := .apply "b" []

/-- Constants carry no argument positions. -/
private theorem constant_covered (language : LanguageDef) (label : String) :
    RowCovered language (.apply label []) :=
  .apply (fun before inner after split => by simp at split)
    (fun argument member => by simp at member)

/-- **Positive: every position of `pair(a, a)` is covered.** -/
theorem pair_covered : RowCovered pairLanguage (.apply "pair" [aTerm, aTerm]) := by
  refine .apply (fun before inner after split => ?_) (fun argument member => ?_)
  · rcases before with _ | ⟨first, _ | ⟨second, rest⟩⟩
    · simp only [List.nil_append, List.cons.injEq] at split
      obtain ⟨_, rfl⟩ := split
      exact ⟨leftRow, by simp [pairs], leftRow_row⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at split
      obtain ⟨_, _, rfl⟩ := split
      exact ⟨rightRow, by simp [pairs], rightRow_row⟩
    · simp at split
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst member
    exact constant_covered _ _

/-- **Positive: on `pair(a, a)` the engine is the congruence closure of the
bubble.** -/
theorem pair_engine_is_closure (base : BasePremiseEvaluator) (target : Pattern) :
    Step base pairLanguage (.apply "pair" [aTerm, aTerm]) target ↔
      patternClosure.step (languageBubble pairLanguage) (.apply "pair" [aTerm, aTerm]) target :=
  step_iff_patternStep pairLanguage_presented pair_covered

/-- **Positive: the engine steps inside a pair at both positions**, as the
congruence closure of the bubble does. -/
theorem pair_steps :
    rewriteAt (engineBasePremises RelationEnv.empty) pairLanguage 2
        (.apply "pair" [aTerm, aTerm]) =
      [.apply "pair" [bTerm, aTerm], .apply "pair" [aTerm, bTerm]] := by
  decide +kernel

/-- The congruence closure of the bubble steps inside a pair whatever the
rows. -/
theorem bubble_steps_inside (rows : List RewriteRule) (root : rootRow ∈ rows) :
    patternClosure.step (languageBubble (pairs rows)) (.apply "pair" [aTerm, aTerm])
      (.apply "pair" [bTerm, aTerm]) := by
  refine ⟨.apply "pair" [] .hole [aTerm], aTerm, bTerm, ?_, rfl, rfl⟩
  simp only [languageBubble, rewriteStep, List.mem_flatMap]
  exact ⟨rootRow, root, by decide +kernel⟩

/-- **Negative: without congruence rows the engine does not step inside a
pair**, while the congruence closure of the bubble does.  Coverage is
load-bearing. -/
theorem rootOnly_engine_stays :
    ¬ Step (engineBasePremises RelationEnv.empty) (pairs [rootRow])
        (.apply "pair" [aTerm, aTerm]) (.apply "pair" [bTerm, aTerm]) ∧
      patternClosure.step (languageBubble (pairs [rootRow])) (.apply "pair" [aTerm, aTerm])
        (.apply "pair" [bTerm, aTerm]) := by
  refine ⟨not_step_of_matchPatternForRule_eq_nil fun rule member => ?_,
    bubble_steps_inside _ (by simp)⟩
  simp only [pairs, List.mem_singleton] at member
  subst member
  rw [matchPatternForRule_eq_syntactic]
  decide +kernel

/-- A non-linear congruence row: `pair(x, x)` steps at its first position. -/
def diagonalRow : RewriteRule :=
  { name := "pairDiagonal", typeContext := [],
    premises := [.congruence (.fvar "x") (.fvar "y")],
    left := .apply "pair" [.fvar "x", .fvar "x"], right := .apply "pair" [.fvar "y", .fvar "x"] }

/-- The diagonal row is no congruence row. -/
theorem diagonalRow_not_row (constructor : String) (beforeCount afterCount : Nat) :
    ¬ IsCongruenceRow diagonalRow constructor beforeCount afterCount := by
  rintro ⟨before, after, source, target, _, _, nodup, _, _, left, _⟩
  have names : (before ++ source :: after).map Pattern.fvar = [.fvar "x", .fvar "x"] := by
    simp only [diagonalRow, Pattern.apply.injEq] at left
    exact left.2.symm
  have twice : before ++ source :: after = ["x", "x"] := by
    have mapped := congrArg (List.map fun pattern => match pattern with
      | .fvar name => name
      | _ => "") names
    simpa [List.map_map, Function.comp_def] using mapped
  rw [twice] at nodup
  exact absurd nodup (by decide)

/-- **Negative: a non-linear congruence row steps where no row context
reaches.**  The engine steps `pair(a, a)` to `pair(b, a)` through the diagonal
row, but the language has no congruence row, so the row closure of its bubble
has only root steps, and `pair(a, a)` has none.  Row presentation is
load-bearing. -/
theorem diagonal_engine_outruns_rows :
    Step (engineBasePremises RelationEnv.empty) (pairs [rootRow, diagonalRow])
        (.apply "pair" [aTerm, aTerm]) (.apply "pair" [bTerm, aTerm]) ∧
      ¬ RowStep (pairs [rootRow, diagonalRow]) (.apply "pair" [aTerm, aTerm])
        (.apply "pair" [bTerm, aTerm]) := by
  refine ⟨exists_mem_rewriteAt_iff_step.mp ⟨2, by decide +kernel⟩, ?_⟩
  rintro ⟨context, redex, contractum, rowContext, bubble, fillRedex, _⟩
  cases rowContext with
  | hole =>
      simp only [OneHoleContext.fill] at fillRedex
      subst fillRedex
      have noRootStep :
          rewriteStep (pairs [rootRow, diagonalRow]) (.apply "pair" [aTerm, aTerm]) = [] := by
        decide +kernel
      simp [languageBubble, noRootStep] at bubble
  | frame rule member row _ =>
      simp only [pairs, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · obtain ⟨_, _, _, _, _, _, _, _, premises, _, _⟩ := row
        simp [rootRow] at premises
      · exact diagonalRow_not_row _ _ _ row

#print axioms step_of_rowStep
#print axioms rowStep_of_stepAt
#print axioms step_iff_rowStep
#print axioms rewriteAt_iff_rowStep
#print axioms eqvGen_step_eq_rowStep
#print axioms step_iff_patternStep
#print axioms pair_engine_is_closure
#print axioms pair_steps
#print axioms rootOnly_engine_stays
#print axioms diagonal_engine_outruns_rows

end Mettapedia.TypeTheory.BubbleJoinEngine
