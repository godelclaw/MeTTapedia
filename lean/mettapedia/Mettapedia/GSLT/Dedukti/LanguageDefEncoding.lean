import Mettapedia.GSLT.Dedukti.TypingSubstitution
import Mettapedia.GSLT.Dedukti.OrthogonalCheck
import Mettapedia.GSLT.LanguageDef.DerivedHosting
import Mettapedia.GSLT.LanguageDef.Contexts.Presented
import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.Framework.PredFiniteSufficient

/-!
# A theory of the λΠ-calculus modulo as a language definition

`DerivedHosting.lfLanguageDef` declares the sorts `LFSort`, `LFTerm`,
`LFName`, `LFIndex` and the constructors `Srt`, `Con`, `Var`, `Pi`, `Lam`,
`App` of λΠ terms, with binders for the bodies of `Pi` and `Lam`.  This module
builds, for a list of constant names and a list of declared rules, the
language definition `dkLanguage names rules`:

* its sorts and constructors are those of `lfLanguageDef`, and one nullary
  constructor of sort `LFName` for each name (`nameRule`);
* it has no equation;
* its rewrites are beta with an explicit substitution node (`betaRule`), the
  six congruences that let a step happen inside an application, a product or
  an abstraction (`appFunctionRule` … `lamBodyRule`, each with one congruence
  premise, as the language definitions of the process calculi author theirs),
  and one rule for each declared rule (`declaredRule`).

Why the beta rule and the equations of `lfLanguageDef` are not kept is stated
and proved in `LanguageDefContextTheory`: its `Beta` writes its contractum with the
authored `eval(B, X)`, which the Lean semantics of rules does not interpret
(it builds the node `$eval`), so no well-sorted term ever steps by it.

**The encoding** (`encode`): a variable is a bound variable of the pattern,
loose when it is free; a constant is `Con` of its name constructor; the body
of a product or an abstraction is beneath a binder.  The encoding is
injective, and it carries lifting and substitution to the shift and the
binder-eliminating instantiation of patterns (`liftBVars_encode`,
`instantiateBVarAt_encode`).  A declared rule becomes a pattern rule whose
pattern variables are metavariables (`toPattern`); on encodings, a match of
its left side is an instance of the declared left side
(`exists_assignment_of_applyBindings`), and applying its right side is
instantiating the declared right side (`applyBindingsScoped_toPattern`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.Language

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern GrammarRule LanguageDef Premise)
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVarsList instantiateBVarAt instantiateBVar)
open Mettapedia.OSLF.Framework.PredFiniteSufficient (lookupOrFvar BindingsValued)

/-! ## The encoding -/

/-- The label of the name constructor of a constant. -/
def nameLabel (symbol : String) : String := "c:" ++ symbol

/-- **The encoding of λΠ terms as patterns.** -/
def encode : Term → Pattern
  | .var index => .bvar index
  | .srt .type => .apply "Srt" [.apply "SortType" []]
  | .srt .kind => .apply "Srt" [.apply "SortKind" []]
  | .con symbol => .apply "Con" [.apply (nameLabel symbol) []]
  | .pi domain body => .apply "Pi" [encode domain, .lambda none (encode body)]
  | .lam domain body => .apply "Lam" [encode domain, .lambda none (encode body)]
  | .app function argument => .apply "App" [encode function, encode argument]

theorem nameLabel_injective : Function.Injective nameLabel := by
  intro first second same
  have lists := congrArg String.toList same
  simp only [nameLabel, String.toList_append] at lists
  exact String.toList_injective (List.append_cancel_left lists)

/-- A left inverse of the encoding. -/
def decode : Pattern → Term
  | .bvar index => .var index
  | .apply "Srt" [.apply "SortType" []] => .srt .type
  | .apply "Srt" [.apply "SortKind" []] => .srt .kind
  | .apply "Con" [.apply label []] => .con (String.ofList (label.toList.drop 2))
  | .apply "Pi" [domain, .lambda _ body] => .pi (decode domain) (decode body)
  | .apply "Lam" [domain, .lambda _ body] => .lam (decode domain) (decode body)
  | .apply "App" [function, argument] => .app (decode function) (decode argument)
  | _ => .srt .type
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem decode_encode (term : Term) : decode (encode term) = term := by
  induction term with
  | var index => simp [encode, decode]
  | srt sort => cases sort <;> simp [encode, decode]
  | con symbol => simp [encode, decode, nameLabel]
  | pi domain body ihDomain ihBody => simp [encode, decode, ihDomain, ihBody]
  | lam domain body ihDomain ihBody => simp [encode, decode, ihDomain, ihBody]
  | app function argument ihFunction ihArgument => simp [encode, decode, ihFunction, ihArgument]

/-- **The encoding is injective.** -/
theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

/-- The encoding has no metavariable. -/
theorem encode_ne_fvar (term : Term) (variable_ : String) : encode term ≠ .fvar variable_ := by
  cases term with
  | srt sort => cases sort <;> simp [encode]
  | _ => simp [encode]

/-- **Lifting is the shift of loose bound variables.** -/
theorem liftBVars_encode (term : Term) :
    ∀ cutoff amount : Nat, liftBVars cutoff amount (encode term) = encode (lift amount cutoff term) := by
  induction term with
  | var index =>
      intro cutoff amount
      by_cases below : index < cutoff
      · have notAbove : ¬ index ≥ cutoff := by omega
        simp [encode, liftBVars, lift, below, notAbove]
      · have above : index ≥ cutoff := by omega
        simp [encode, liftBVars, lift, below, above]
  | srt sort => intro cutoff amount; cases sort <;> simp [encode, liftBVars, liftBVarsList, lift]
  | con symbol => intro cutoff amount; simp [encode, liftBVars, liftBVarsList, lift]
  | pi domain body ihDomain ihBody =>
      intro cutoff amount; simp [encode, liftBVars, liftBVarsList, lift, ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      intro cutoff amount; simp [encode, liftBVars, liftBVarsList, lift, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro cutoff amount; simp [encode, liftBVars, liftBVarsList, lift, ihFunction, ihArgument]

/-- **Substitution is the binder-eliminating instantiation of patterns.** -/
theorem instantiateBVarAt_encode (body : Term) :
    ∀ (depth : Nat) (replacement : Term),
      instantiateBVarAt depth (encode replacement) (encode body) =
        encode (subst depth (lift depth 0 replacement) body) := by
  induction body with
  | var index =>
      intro depth replacement
      by_cases below : index < depth
      · have notSame : index ≠ depth := by omega
        have notAbove : ¬ depth < index := by omega
        simp [encode, instantiateBVarAt, subst, below, notSame, notAbove]
      · by_cases same : index = depth
        · subst same
          simp [encode, instantiateBVarAt, subst, liftBVars_encode]
        · have above : depth < index := by omega
          simp [encode, instantiateBVarAt, subst, below, same, above]
  | srt sort => intro depth replacement; cases sort <;> simp [encode, instantiateBVarAt, subst]
  | con symbol => intro depth replacement; simp [encode, instantiateBVarAt, subst]
  | pi domain body ihDomain ihBody =>
      intro depth replacement
      have lifted : lift 1 0 (lift depth 0 replacement) = lift (depth + 1) 0 replacement := by
        rw [lift_lift_same, Nat.add_comm]
      simp [encode, instantiateBVarAt, subst, ihDomain, ihBody, lifted]
  | lam domain body ihDomain ihBody =>
      intro depth replacement
      have lifted : lift 1 0 (lift depth 0 replacement) = lift (depth + 1) 0 replacement := by
        rw [lift_lift_same, Nat.add_comm]
      simp [encode, instantiateBVarAt, subst, ihDomain, ihBody, lifted]
  | app function argument ihFunction ihArgument =>
      intro depth replacement
      simp [encode, instantiateBVarAt, subst, ihFunction, ihArgument]

/-- **Beta is the instantiation of the outermost binder.** -/
theorem instantiateBVar_encode (argument body : Term) :
    instantiateBVar (encode argument) (encode body) = encode (subst0 argument body) := by
  have general := instantiateBVarAt_encode body 0 argument
  rw [lift_zero] at general
  exact general

/-! ## Declared rules as pattern rules -/

/-- The name of the metavariable of a pattern variable. -/
def metaName (index : Nat) : String := String.ofList (List.replicate (index + 1) 'x')

theorem metaName_injective : Function.Injective metaName := by
  intro first second same
  have lists := String.ofList_injective same
  have lengths := congrArg List.length lists
  simp only [List.length_replicate] at lengths
  omega

/-- A side of a declared rule as a pattern, beneath `depth` binders: a free
variable is the metavariable of a pattern variable. -/
def toPattern (depth : Nat) : Term → Pattern
  | .var index => if index < depth then .bvar index else .fvar (metaName (index - depth))
  | .srt sort => encode (.srt sort)
  | .con symbol => encode (.con symbol)
  | .pi domain body => .apply "Pi" [toPattern depth domain, .lambda none (toPattern (depth + 1) body)]
  | .lam domain body => .apply "Lam" [toPattern depth domain, .lambda none (toPattern (depth + 1) body)]
  | .app function argument => .apply "App" [toPattern depth function, toPattern depth argument]

/-- The pattern of an algebraic left side is matched exactly. -/
theorem toPattern_matchCorrect : ∀ {term : Term} {headed : Bool}, algebraic headed term = true →
    isMatchCorrectAux (toPattern 0 term) = true := by
  intro term
  induction term with
  | var index => intro headed _; simp [toPattern, isMatchCorrectAux]
  | srt sort => intro headed _; cases sort <;> simp [toPattern, encode, isMatchCorrectAux,
      isMatchCorrectListAux]
  | con symbol => intro headed _; simp [toPattern, encode, isMatchCorrectAux, isMatchCorrectListAux]
  | pi domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | lam domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | app function argument ihFunction ihArgument =>
      intro headed isAlgebraic
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := algebraic_app.mp isAlgebraic
      simp [toPattern, isMatchCorrectAux, isMatchCorrectListAux, ihFunction functionAlgebraic,
        ihArgument argumentAlgebraic]

/-- In the pattern of an algebraic left side, every metavariable sits at depth
zero. -/
theorem captureDepth_toPattern (symbol : String) : ∀ {term : Term} {headed : Bool},
    algebraic headed term = true → ∀ found, captureDepth symbol 0 (toPattern 0 term) = some found →
      found = 0 := by
  intro term headed isAlgebraic found captured
  have binderFree : binderFree (toPattern 0 term) = true :=
    binderFree_of_isMatchCorrectAux _ (toPattern_matchCorrect isAlgebraic)
  exact captureDepth_of_binderFree symbol 0 _ binderFree found captured

/-- A metavariable of a pattern variable of an algebraic left side is captured
at depth zero. -/
theorem captureDepth_toPattern_of_mem : ∀ {term : Term} {headed : Bool},
    algebraic headed term = true → ∀ index ∈ patternVars term,
      captureDepth (metaName index) 0 (toPattern 0 term) = some 0 := by
  intro term
  induction term with
  | var other =>
      intro headed _ index member
      rw [List.mem_singleton.mp member]
      simp [toPattern, captureDepth]
  | srt sort => intro headed _ index member; simp [patternVars] at member
  | con symbol => intro headed _ index member; simp [patternVars] at member
  | pi domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | lam domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | app function argument ihFunction ihArgument =>
      intro headed isAlgebraic index member
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := algebraic_app.mp isAlgebraic
      simp only [toPattern, captureDepth, captureDepthList]
      rcases List.mem_append.mp member with inFunction | inArgument
      · rw [ihFunction functionAlgebraic index inFunction]
      · cases first : captureDepth (metaName index) 0 (toPattern 0 function) with
        | none => simp [ihArgument argumentAlgebraic index inArgument]
        | some found =>
            simp only
            rw [captureDepth_toPattern (metaName index) functionAlgebraic found first]

/-- **What a match of an algebraic left side against an encoding is.**  The
matched term is an instance of the left side, and each metavariable of a
pattern variable is bound to the encoding of what the instance puts there. -/
theorem exists_assignment_of_applyBindings (bindings : Bindings) :
    ∀ {term : Term} {headed : Bool}, algebraic headed term = true →
      ∀ source : Term, applyBindings bindings (toPattern 0 term) = encode source →
        ∃ assignment : Nat → Term, source = inst assignment term ∧
          ∀ index ∈ patternVars term,
            lookupOrFvar bindings (metaName index) = encode (assignment index) := by
  intro term
  induction term with
  | var index =>
      intro headed _ source same
      refine ⟨fun _ => source, by simp, ?_⟩
      intro other member
      rw [List.mem_singleton.mp member]
      simpa [toPattern, lookupOrFvar] using same
  | srt sort =>
      intro headed _ source same
      refine ⟨fun _ => source, ?_, fun _ member => by simp [patternVars] at member⟩
      have encoded : encode source = encode (.srt sort) := by
        rw [← same]
        cases sort <;> simp [toPattern, encode, applyBindings]
      rw [encode_injective encoded]
      rfl
  | con symbol =>
      intro headed _ source same
      refine ⟨fun _ => source, ?_, fun _ member => by simp [patternVars] at member⟩
      have encoded : encode source = encode (.con symbol) := by
        rw [← same]
        simp [toPattern, encode, applyBindings]
      rw [encode_injective encoded]
      rfl
  | pi domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | lam domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | app function argument ihFunction ihArgument =>
      intro headed isAlgebraic source same
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := algebraic_app.mp isAlgebraic
      cases source with
      | app sourceFunction sourceArgument =>
          simp only [toPattern, applyBindings, List.map_cons, List.map_nil, encode,
            Pattern.apply.injEq, List.cons.injEq, true_and, and_true] at same
          obtain ⟨functionSame, argumentSame⟩ := same
          obtain ⟨first, functionEq, functionValues⟩ :=
            ihFunction functionAlgebraic sourceFunction functionSame
          obtain ⟨second, argumentEq, argumentValues⟩ :=
            ihArgument argumentAlgebraic sourceArgument argumentSame
          classical
          refine ⟨fun index => if index ∈ patternVars function then first index else second index,
            ?_, ?_⟩
          · rw [inst_app, functionEq, argumentEq]
            congr 1
            · exact inst_congr_patternVars functionAlgebraic fun index member => by simp [member]
            · refine inst_congr_patternVars argumentAlgebraic fun index member => ?_
              by_cases inFunction : index ∈ patternVars function
              · simp only [inFunction, if_true]
                exact (encode_injective ((functionValues index inFunction).symm.trans
                  (argumentValues index member))).symm
              · simp [inFunction]
          · intro index member
            by_cases inFunction : index ∈ patternVars function
            · simp only [inFunction, if_true]
              exact functionValues index inFunction
            · have inArgument : index ∈ patternVars argument := by
                rcases List.mem_append.mp member with here | there
                · exact absurd here inFunction
                · exact there
              simp only [inFunction, if_false]
              exact argumentValues index inArgument
      | var index => simp [toPattern, applyBindings, encode] at same
      | srt sort => cases sort <;> simp [toPattern, applyBindings, encode] at same
      | con symbol => simp [toPattern, applyBindings, encode] at same
      | pi domain' body' => simp [toPattern, applyBindings, encode] at same
      | lam domain' body' => simp [toPattern, applyBindings, encode] at same

/-- **Applying the right side of a declared rule is instantiating it.** -/
theorem applyBindingsScoped_toPattern {lhs : Term} (algebraicLeft : algebraic true lhs = true)
    (bindings : Bindings) (assignment : Nat → Term)
    (values : ∀ index ∈ patternVars lhs,
      lookupOrFvar bindings (metaName index) = encode (assignment index)) :
    ∀ (rhs : Term) (depth : Nat), usesOnly (patternVars lhs) depth rhs = true →
      applyBindingsScoped (toPattern 0 lhs) bindings depth (toPattern depth rhs) =
        encode (instantiate assignment depth rhs) := by
  intro rhs
  induction rhs with
  | var index =>
      intro depth uses
      by_cases below : index < depth
      · simp [toPattern, instantiate, below, encode]
      · simp only [usesOnly, below, decide_false, Bool.false_or, decide_eq_true_eq] at uses
        have value := values _ uses
        have captured := captureDepth_toPattern_of_mem algebraicLeft _ uses
        simp only [toPattern, below, if_false, instantiate]
        unfold lookupOrFvar at value
        simp only [applyBindings] at value
        cases found : bindings.find? (fun entry => entry.1 == metaName (index - depth)) with
        | none =>
            rw [found] at value
            exact absurd value.symm (encode_ne_fvar _ _)
        | some entry =>
            rw [found] at value
            simp only at value
            simp only [applyBindingsScoped, found, captured, Nat.sub_zero, value, liftBVars_encode]
  | srt sort => intro depth _; cases sort <;> simp [toPattern, instantiate, encode, applyBindingsScoped]
  | con symbol => intro depth _; simp [toPattern, instantiate, encode, applyBindingsScoped]
  | pi domain body ihDomain ihBody =>
      intro depth uses
      simp only [usesOnly, Bool.and_eq_true] at uses
      simp [toPattern, instantiate, encode, applyBindingsScoped_apply, applyBindingsScoped,
        ihDomain depth uses.1, ihBody (depth + 1) uses.2]
  | lam domain body ihDomain ihBody =>
      intro depth uses
      simp only [usesOnly, Bool.and_eq_true] at uses
      simp [toPattern, instantiate, encode, applyBindingsScoped_apply, applyBindingsScoped,
        ihDomain depth uses.1, ihBody (depth + 1) uses.2]
  | app function argument ihFunction ihArgument =>
      intro depth uses
      simp only [usesOnly, Bool.and_eq_true] at uses
      simp [toPattern, instantiate, encode, applyBindingsScoped_apply,
        ihFunction depth uses.1, ihArgument depth uses.2]

end Mettapedia.GSLT.Dedukti.Language
