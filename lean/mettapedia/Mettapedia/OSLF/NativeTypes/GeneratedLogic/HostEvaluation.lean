import Mettapedia.OSLF.MeTTaIL.ReferenceStep
import Mettapedia.OSLF.MeTTaIL.LinearMatch

/-!
# Constructors their host evaluates

A constructor of a language declares how it is evaluated (`GrammarRule.evalPolicy?`): by the language's rules
(`rewrite`, the default), or by its host, natively (`fold`) or effectfully (`oracle`). The language carries no host
implementation, so nothing in it says what such a constructor evaluates to. The front door meets its host where it
meets every external relation, in the relation environment it is asked with.

- **The host rule of a host-evaluated constructor** (`hostRule`): `f(x₁, …, xₙ) ⇒ y` when the host relation
  `host:f` holds of `(x₁, …, xₙ, y)`. A language with its host rules (`withHost`) keeps its own rules first.
- **The host rules step exactly as the host answers** (`hostStep_iff`): a step by the host rule of `f` goes from
  `f(v₁, …, vₙ)` to `w` exactly when the host's tuples for the request `(v₁, …, vₙ, y)` include `(v₁, …, vₙ, w)`.
- **Without a host nothing is evaluated** (`no_hostStep_of_empty`), and a language with no host-evaluated constructor
  is unchanged (`withHost_of_none`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.HostEvaluation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule)

/-! ## Host rules -/

/-- **Whether the host evaluates a constructor**: natively or effectfully. -/
def hostEvaluated (rule : GrammarRule) : Bool :=
  match rule.evalPolicy? with
  | some .fold | some .oracle => true
  | _ => false

/-- The relation the host answers for a constructor. -/
def relationOf (rule : GrammarRule) : String := "host:" ++ rule.label

/-- The metavariable of an argument position. -/
def argumentName (index : ℕ) : String := "host:argument".pushn '\'' index

/-- The metavariables of a constructor's arguments. -/
def argumentNames (rule : GrammarRule) : List String := (List.range rule.params.length).map argumentName

/-- The metavariable of the host's answer. -/
def resultName : String := "host:result"

/-- **The host rule of a constructor**: `f(x₁, …, xₙ) ⇒ y` when `host:f(x₁, …, xₙ, y)`. -/
def hostRule (rule : GrammarRule) : RewriteRule where
  name := relationOf rule
  typeContext := (argumentNames rule).zip (rule.params.map TermParam.typeExpr) ++ [(resultName, .base rule.category)]
  premises := [.relationQuery (relationOf rule) ((argumentNames rule).map .fvar ++ [.fvar resultName])]
  left := .apply rule.label ((argumentNames rule).map .fvar)
  right := .fvar resultName

/-- The host rules of a language's host-evaluated constructors. -/
def hostRules (language : LanguageDef) : List RewriteRule := (language.terms.filter hostEvaluated).map hostRule

/-- **A language with its host rules**, after its own. -/
def withHost (language : LanguageDef) : LanguageDef :=
  { language with «rewrites» := language.rewrites ++ hostRules language }

/-- A language with no host-evaluated constructor is unchanged. -/
theorem withHost_of_none {language : LanguageDef} (none : language.terms.filter hostEvaluated = []) :
    withHost language = language := by
  simp [withHost, hostRules, none]

theorem withHost_equations (language : LanguageDef) : (withHost language).equations = language.equations := rfl

/-! ## Names -/

theorem argumentName_injective : Function.Injective argumentName := by
  intro first second same
  have lengths := congrArg String.length same
  simp only [argumentName, String.length_pushn] at lengths
  omega

theorem argumentNames_nodup (rule : GrammarRule) : (argumentNames rule).Nodup :=
  (List.nodup_range).map argumentName_injective

theorem length_argumentNames (rule : GrammarRule) : (argumentNames rule).length = rule.params.length := by
  simp [argumentNames]

theorem resultName_not_argument (rule : GrammarRule) : resultName ∉ argumentNames rule := by
  intro member
  obtain ⟨index, -, same⟩ := List.mem_map.mp member
  have lengths := congrArg String.length same
  simp only [argumentName, String.length_pushn, resultName] at lengths
  have : "host:argument".length = 13 := by decide
  have : "host:result".length = 11 := by decide
  omega

theorem relationOf_ne_eq (rule : GrammarRule) : relationOf rule ≠ "eq" := by
  intro same
  have lengths := congrArg String.length same
  simp only [relationOf, String.length_append] at lengths
  have : "host:".length = 5 := by decide
  have : "eq".length = 2 := by decide
  omega

theorem builtinRelationTuples_host (language : LanguageDef) (rule : GrammarRule) (arguments : List Pattern) :
    builtinRelationTuples language (relationOf rule) arguments = [] := by
  unfold builtinRelationTuples
  split
  · rename_i same
    exact absurd same (relationOf_ne_eq rule)
  · rfl

/-! ## Lookup tables -/

theorem find?_of_not_mem : ∀ {table : Bindings} {name : String}, name ∉ table.map Prod.fst →
    table.find? (fun entry => entry.1 == name) = none
  | [], _, _ => rfl
  | (head, _) :: rest, name, absent => by
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    rw [List.find?_cons, beq_false_of_ne (Ne.symm absent.1)]
    exact find?_of_not_mem absent.2

theorem lookup_of_mem {table : Bindings} {name : String} {value : Pattern} (nodup : (table.map Prod.fst).Nodup)
    (member : (name, value) ∈ table) : table.lookup name = some value := by
  unfold Bindings.lookup
  rw [Mettapedia.OSLF.MeTTaIL.LinearMatch.find?_of_mem_of_nodup table nodup member]
  rfl

theorem lookup_of_not_mem {table : Bindings} {name : String} (absent : name ∉ table.map Prod.fst) :
    table.lookup name = none := by
  unfold Bindings.lookup
  rw [find?_of_not_mem absent]
  rfl

theorem not_mem_of_lookup {table : Bindings} {name : String} (none : table.lookup name = none) :
    name ∉ table.map Prod.fst := by
  intro member
  obtain ⟨pair, inTable, same⟩ := List.mem_map.mp member
  unfold Bindings.lookup at none
  have absent := List.find?_eq_none.mp (Option.map_eq_none_iff.mp none) pair inTable
  simp [same] at absent

/-! ## The host's answer as a match -/

/-- **A request whose arguments are bound and whose answer is free matches exactly the tuples that extend the
arguments by one answer**, and binds only the answer. -/
theorem mem_matchRelationArgs_iff {seed : Bindings} {result : String}
    (unbound : seed.lookup result = none) :
    ∀ (names : List String) (arguments : List Pattern),
      result ∉ names → names.length = arguments.length →
      (∀ pair ∈ names.zip arguments, seed.lookup pair.1 = some pair.2) →
      ∀ (tuple : List Pattern) (extension : Bindings),
        extension ∈ matchRelationArgs seed (names.map Pattern.fvar ++ [.fvar result]) tuple ↔
          ∃ answer, tuple = arguments ++ [answer] ∧ extension = [(result, answer)]
  | [], [], _, _, _, tuple, extension => by
    have found := find?_of_not_mem (not_mem_of_lookup unbound)
    cases tuple with
    | nil => simp [matchRelationArgs]
    | cons answer rest =>
      cases rest with
      | nil => simp [matchRelationArgs, matchRelationArgument, unbound, mergeBindings, found]
      | cons extra more => simp [matchRelationArgs, matchRelationArgument, unbound, mergeBindings, found]
  | [], _ :: _, _, lengths, _, _, _ => by simp at lengths
  | _ :: _, [], _, lengths, _, _, _ => by simp at lengths
  | name :: names, argument :: arguments, absent, lengths, bound, tuple, extension => by
    have headBound : seed.lookup name = some argument := bound (name, argument) (by simp)
    have rest := mem_matchRelationArgs_iff unbound names arguments
      (fun member => absent (List.mem_cons_of_mem _ member)) (by simpa using lengths)
      (fun pair member => bound pair (by simp [member]))
    cases tuple with
    | nil => simp [matchRelationArgs]
    | cons value values =>
      simp only [List.map_cons, List.cons_append, matchRelationArgs, matchRelationArgument, headBound]
      by_cases same : argument = value
      · subst same
        have mergedSeed : mergeBindings seed [] = some seed := rfl
        simp only [if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil, mergedSeed, List.mem_filterMap]
        constructor
        · rintro ⟨tail, inTail, merged⟩
          obtain ⟨answer, rfl, rfl⟩ := (rest values tail).mp inTail
          refine ⟨answer, rfl, ?_⟩
          simp [mergeBindings] at merged
          exact merged.symm
        · rintro ⟨answer, sameTuple, rfl⟩
          simp only [List.cons.injEq, true_and] at sameTuple
          subst sameTuple
          exact ⟨[(result, answer)], (rest _ _).mpr ⟨answer, rfl, rfl⟩, by simp [mergeBindings]⟩
      · simp only [same, if_false, List.flatMap_nil, List.not_mem_nil, false_iff, not_exists, not_and]
        intro answer sameTuple
        simp only [List.cons.injEq] at sameTuple
        exact absurd sameTuple.1.symm same

/-! ## The host rules step exactly as the host answers -/

/-- What matching a host rule's left side says: the source is the constructor applied to as many arguments as it
takes, and the bindings are those arguments at their metavariables, nothing else. -/
theorem matchPattern_hostRule {rule : GrammarRule} {source : Pattern} {initial : Bindings}
    (matched : initial ∈ matchPattern (hostRule rule).left source) :
    ∃ arguments, source = .apply rule.label arguments ∧ arguments.length = rule.params.length ∧
      (∀ pair ∈ initial, pair.1 ∈ argumentNames rule) ∧ (initial.map Prod.fst).Nodup ∧
        (∀ pair ∈ (argumentNames rule).zip arguments, pair ∈ initial) := by
  cases source with
  | apply label arguments =>
    simp only [hostRule, matchPattern] at matched
    split at matched
    · rename_i fits
      simp only [Bool.and_eq_true, beq_iff_eq, List.length_map, length_argumentNames] at fits
      obtain ⟨rfl, lengths⟩ := fits
      obtain ⟨names, nodup, pairs⟩ := Mettapedia.OSLF.MeTTaIL.LinearMatch.matchArgsRel_fvars_inversion
        (argumentNames rule) arguments initial (Mettapedia.OSLF.MeTTaIL.MatchSpec.matchArgs_sound matched)
        (argumentNames_nodup rule)
      exact ⟨arguments, rfl, lengths.symm, names, nodup, pairs⟩
    · simp at matched
  | _ => simp [hostRule, matchPattern] at matched

theorem applyBindings_request {rule : GrammarRule} {initial : Bindings} {arguments : List Pattern}
    (lengths : arguments.length = rule.params.length) (names : ∀ pair ∈ initial, pair.1 ∈ argumentNames rule)
    (nodup : (initial.map Prod.fst).Nodup) (pairs : ∀ pair ∈ (argumentNames rule).zip arguments, pair ∈ initial) :
    ((argumentNames rule).map Pattern.fvar ++ [Pattern.fvar resultName]).map (applyBindings initial) =
      arguments ++ [Pattern.fvar resultName] := by
  have absent : resultName ∉ initial.map Prod.fst := by
    intro member
    obtain ⟨pair, inInitial, same⟩ := List.mem_map.mp member
    exact resultName_not_argument rule (same ▸ names pair inInitial)
  rw [List.map_append, Mettapedia.OSLF.MeTTaIL.LinearMatch.applyBindings_fvars initial nodup _ _
    (by rw [length_argumentNames, lengths]) pairs]
  simp only [List.map_cons, List.map_nil, applyBindings, find?_of_not_mem absent]

/-- **The host rules step exactly as the host answers**: a step by the host rule of a constructor goes from the
constructor applied to arguments to an answer exactly when the host's tuples for the request, the arguments with the
answer left open, include the arguments with that answer. -/
theorem hostStep_iff (relEnv : RelationEnv) (language : LanguageDef) {index : ℕ} {rule : GrammarRule}
    (found : (withHost language).rewrites[index]? = some (hostRule rule)) (source target : Pattern) :
    (∃ initial witnesses, StepValid relEnv (withHost language) source (.rule index initial witnesses) target) ↔
      ∃ arguments, source = .apply rule.label arguments ∧ arguments.length = rule.params.length ∧
        arguments ++ [target] ∈ relEnv.tuples (relationOf rule) (arguments ++ [.fvar resultName]) := by
  constructor
  · rintro ⟨initial, witnesses, valid⟩
    cases valid with
    | rule found' matched premises =>
      obtain rfl := Option.some.inj (found'.symm.trans found)
      rw [matchPatternForRule, Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic_of_no_presentations rfl] at matched
      obtain ⟨arguments, rfl, lengths, names, nodup, pairs⟩ := matchPattern_hostRule matched
      have absent : resultName ∉ initial.map Prod.fst := by
        intro member
        obtain ⟨pair, inInitial, same⟩ := List.mem_map.mp member
        exact resultName_not_argument rule (same ▸ names pair inInitial)
      cases premises with
      | cons premise rest =>
        cases rest with
        | nil =>
          cases premise with
          | base _ member =>
            simp only [premiseStepWithEnv, relationQueryStep] at member
            rw [applyBindings_request lengths names nodup pairs, builtinRelationTuples_host, List.nil_append] at member
            simp only [List.mem_flatMap, List.mem_filterMap] at member
            obtain ⟨tuple, provided, extension, matchedTuple, merged⟩ := member
            obtain ⟨answer, rfl, rfl⟩ := (mem_matchRelationArgs_iff (lookup_of_not_mem absent) (argumentNames rule)
              arguments (resultName_not_argument rule) (by rw [length_argumentNames, lengths])
              (fun pair member => lookup_of_mem nodup (pairs pair member)) tuple extension).mp matchedTuple
            simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil, find?_of_not_mem absent] at merged
            obtain rfl := (Option.some.inj merged).symm
            refine ⟨arguments, rfl, lengths, ?_⟩
            simpa [hostRule, applyBindings] using provided
          | step endpoints => simp [stepEndpoints] at endpoints
  · rintro ⟨arguments, rfl, lengths, provided⟩
    obtain ⟨initial, matched, nodup, namesIff, pairs⟩ := Mettapedia.OSLF.MeTTaIL.LinearMatch.matchArgs_fvars
      (argumentNames rule) arguments (argumentNames_nodup rule) (by rw [length_argumentNames, lengths])
    have names : ∀ pair ∈ initial, pair.1 ∈ argumentNames rule :=
      fun pair member => (namesIff pair.1).mp (List.mem_map_of_mem member)
    have absent : resultName ∉ initial.map Prod.fst := fun member =>
      resultName_not_argument rule ((namesIff _).mp member)
    have matchedRule : initial ∈ matchPatternForRule (withHost language) (hostRule rule) (.apply rule.label arguments) := by
      rw [matchPatternForRule, Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic_of_no_presentations rfl]
      simp only [hostRule, matchPattern]
      rw [if_pos (by simp [length_argumentNames, lengths])]
      exact matched
    have member : ((resultName, target) :: initial) ∈
        premiseStepWithEnv relEnv (withHost language) initial
          (.relationQuery (relationOf rule) ((argumentNames rule).map .fvar ++ [.fvar resultName])) := by
      simp only [premiseStepWithEnv, relationQueryStep]
      rw [applyBindings_request lengths names nodup pairs, builtinRelationTuples_host, List.nil_append]
      simp only [List.mem_flatMap, List.mem_filterMap]
      refine ⟨arguments ++ [target], provided, [(resultName, target)], ?_, ?_⟩
      · exact (mem_matchRelationArgs_iff (lookup_of_not_mem absent) (argumentNames rule) arguments
          (resultName_not_argument rule) (by rw [length_argumentNames, lengths])
          (fun pair member => lookup_of_mem nodup (pairs pair member)) _ _).mpr ⟨target, rfl, rfl⟩
      · simp [mergeBindings, find?_of_not_mem absent]
    have valid := StepValid.rule (relEnv := relEnv) found matchedRule
      (PremisesValid.cons (PremiseValid.base rfl member) (PremisesValid.nil _))
    have reached : applyBindingsScoped (captureSites (hostRule rule)) ((resultName, target) :: initial) 0
        (hostRule rule).right = target := by
      simp [hostRule, applyBindings]
    rw [reached] at valid
    exact ⟨initial, _, valid⟩

/-- **Without a host nothing is evaluated**: with no relation provided, a host rule never steps. -/
theorem no_hostStep_of_empty (language : LanguageDef) {index : ℕ} {rule : GrammarRule}
    (found : (withHost language).rewrites[index]? = some (hostRule rule)) (source target : Pattern) :
    ¬ ∃ initial witnesses, StepValid RelationEnv.empty (withHost language) source (.rule index initial witnesses) target := by
  rw [hostStep_iff RelationEnv.empty language found]
  rintro ⟨_, _, _, provided⟩
  simp [RelationEnv.empty] at provided

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.HostEvaluation
