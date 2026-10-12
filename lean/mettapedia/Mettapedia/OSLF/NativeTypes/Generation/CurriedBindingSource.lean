import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonical

/-!
# Independent source adequacy of computed curried binding signatures

Source patterns retain their authored constructor origin. Canonical locally
nameless patterns are compared with the generated binding signature in every
ambient base context. Noncanonical display names stay in the source receipt;
their semantic comparison uses the separately defined alpha quotient.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open BindingSemanticAdmission

variable {language : LanguageDef}

theorem wrap_object (domains : List String) (body : Pattern) :
    isObjectPattern (wrap domains body) = isObjectPattern body := by
  induction domains <;> simp_all [wrap, isObjectPattern]

theorem wrap_canonical (domains : List String) (body : Pattern) :
    (wrap domains body).hasCanonicalBinderMetadata = body.hasCanonicalBinderMetadata := by
  induction domains <;> simp_all [wrap, Pattern.hasCanonicalBinderMetadata]

theorem argument_object (parameter : TermParam) (body : Pattern) :
    isObjectPattern (printArgument parameter body) = isObjectPattern body := by
  cases parameter with
  | simple => rfl
  | abstractionNamed binder name type =>
      cases type <;> simp only [printArgument, isObjectPattern]
      all_goals cases binderSpine? _ <;> simp only [wrap_object]
  | multiAbstractionNamed => rfl

theorem argument_canonical (parameter : TermParam) (body : Pattern) :
    (printArgument parameter body).hasCanonicalBinderMetadata = body.hasCanonicalBinderMetadata := by
  cases parameter with
  | simple => rfl
  | abstractionNamed binder name type =>
      cases type <;> simp only [printArgument, Pattern.hasCanonicalBinderMetadata,
        Option.isNone_none, Bool.true_and]
      all_goals cases binderSpine? _ <;> simp only [wrap_canonical]
  | multiAbstractionNamed => rfl

theorem printObjectSized (n : Nat) :
    (∀ {context : List String} {sort : String} (term : Term (signature language) context sort),
      termSize term < n → isObjectPattern (toPattern term) = true ∧
        (toPattern term).hasCanonicalBinderMetadata = true) ∧
    (∀ (parameters : List TermParam) {context : List String}
      {arity : List (List String × String)} (arguments : Args (signature language) arity context),
      argsSize arguments < n → isObjectPatternList (toPatterns parameters arguments) = true ∧
        Pattern.hasCanonicalBinderMetadataList (toPatterns parameters arguments) = true) := by
  induction n with
  | zero => constructor <;> intros <;> omega
  | succ n ih =>
      constructor
      · intro context sort term small
        change Ctx (signature language) at context
        change (signature language).Srt at sort
        cases term with
        | var => exact ⟨rfl, rfl⟩
        | op origin arguments =>
            have smaller : argsSize arguments < n := by simp only [termSize] at small; omega
            exact ih.2 _ arguments smaller
      · intro parameters context arity arguments small
        change Ctx (signature language) at context
        change List (List (signature language).Srt × (signature language).Srt) at arity
        cases arguments with
        | nil => cases parameters <;> exact ⟨rfl, rfl⟩
        | cons body rest =>
            cases parameters with
            | nil => exact ⟨rfl, rfl⟩
            | cons parameter parameters =>
                have smallerBody : termSize body < n := by simp only [argsSize] at small; omega
                have smallerRest : argsSize rest < n := by simp only [argsSize] at small; omega
                obtain ⟨bodyObject, bodyCanonical⟩ := ih.1 body smallerBody
                obtain ⟨restObject, restCanonical⟩ := ih.2 parameters rest smallerRest
                change isObjectPatternList (printArgument parameter (toPattern body) :: toPatterns parameters rest) = true ∧
                  Pattern.hasCanonicalBinderMetadataList (printArgument parameter (toPattern body) :: toPatterns parameters rest) = true
                simp only [isObjectPatternList, Pattern.hasCanonicalBinderMetadataList,
                  argument_object, argument_canonical, bodyObject, bodyCanonical, restObject,
                  restCanonical, Bool.true_and]
                trivial

theorem toPattern_object {context : List String} {sort : String}
    (term : Term (signature language) context sort) : isObjectPattern (toPattern term) = true :=
  ((printObjectSized (termSize term + 1)).1 term (Nat.lt_succ_self _)).1

theorem toPattern_canonical {context : List String} {sort : String}
    (term : Term (signature language) context sort) :
    (toPattern term).hasCanonicalBinderMetadata = true :=
  ((printObjectSized (termSize term + 1)).1 term (Nat.lt_succ_self _)).2

theorem wrap_injective (domains : List String) : Function.Injective (wrap domains) := by
  induction domains with
  | nil => exact fun _ _ equality => equality
  | cons domain domains ih =>
      intro left right equality
      exact ih (Pattern.lambda.inj equality).2

theorem argument_injective (parameter : TermParam) : Function.Injective (printArgument parameter) := by
  cases parameter with
  | simple => exact fun _ _ equality => equality
  | abstractionNamed binder name type =>
      cases type with
      | base => exact fun _ _ equality => (Pattern.lambda.inj equality).2
      | arrow domain codomain =>
          intro left right equality
          simp only [printArgument] at equality
          cases decoded : binderSpine? (.arrow domain codomain) with
          | none => simpa only [decoded] using equality
          | some spine => exact wrap_injective spine.1 (by simpa only [decoded] using equality)
      | multiBinder => exact fun _ _ equality => equality
      | collection => exact fun _ _ equality => equality
  | multiAbstractionNamed => exact fun _ _ equality => equality

theorem origin_label_injective (labels : (language.terms.map (·.label)).Nodup)
    {sort : String} (left right : Origin language sort)
    (same : language.terms[left.index.val].label = language.terms[right.index.val].label) :
    left = right := by
  have sameIndex : left.index = right.index := by
    apply Fin.ext
    apply (labels.getElem_inj_iff (hi := by simp only [List.length_map]; exact left.index.isLt)
      (hj := by simp only [List.length_map]; exact right.index.isLt)).mp
    simpa using same
  cases left
  cases right
  cases sameIndex
  rfl

theorem variableIndex_eq_varIndex {context : List String} {sort : String}
    (position : Var (Srt := String) context sort) :
    variableIndex position = Mettapedia.GSLT.Poly.BindingLanguage.varIndex position := by
  induction position <;> simp_all [variableIndex, Mettapedia.GSLT.Poly.BindingLanguage.varIndex]

theorem printInjectiveSized (labels : (language.terms.map (·.label)).Nodup) (n : Nat) :
    (∀ {context : List String} {sort : String} (left right : Term (signature language) context sort),
      termSize left < n → toPattern left = toPattern right → left = right) ∧
    (∀ (parameters : List TermParam) {context : List String} {arity : List (List String × String)}
      (left right : Args (signature language) arity context), arity = slots parameters →
      argsSize left < n → toPatterns parameters left = toPatterns parameters right → left = right) := by
  induction n with
  | zero => constructor <;> intros <;> omega
  | succ n ih =>
      constructor
      · intro context sort left right small same
        change Ctx (signature language) at context
        change (signature language).Srt at sort
        match left, right with
        | .var left, .var right =>
            have indices : variableIndex left = variableIndex right := Pattern.bvar.inj same
            change Var (Srt := String) context sort at left right
            have printed : Mettapedia.GSLT.Poly.BindingLanguage.varIndex left =
                Mettapedia.GSLT.Poly.BindingLanguage.varIndex right := by
              exact (variableIndex_eq_varIndex left).symm.trans
                (indices.trans (variableIndex_eq_varIndex right))
            exact congrArg Term.var (Mettapedia.GSLT.Poly.BindingLanguage.varIndex_injective left right printed)
        | .var _, .op _ _ => cases same
        | .op _ _, .var _ => cases same
        | .op leftOrigin leftArgs, .op rightOrigin rightArgs =>
            obtain ⟨sameLabel, sameArgs⟩ := Pattern.apply.inj same
            have origins := origin_label_injective labels leftOrigin rightOrigin sameLabel
            subst rightOrigin
            have smaller : argsSize leftArgs < n := by simp only [termSize] at small; omega
            exact congrArg (Term.op leftOrigin) (ih.2 _ leftArgs rightArgs rfl smaller sameArgs)
      · intro parameters context arity left right aligned small same
        change Ctx (signature language) at context
        change List (List (signature language).Srt × (signature language).Srt) at arity
        match left, right with
        | .nil, .nil => rfl
        | .cons leftBody leftRest, .cons rightBody rightRest =>
            cases parameters with
            | nil => simp [slots] at aligned
            | cons parameter parameters =>
                obtain ⟨heads, tails⟩ := List.cons.inj same
                have smallerBody : termSize leftBody < n := by simp only [argsSize] at small; omega
                have smallerRest : argsSize leftRest < n := by simp only [argsSize] at small; omega
                have bodies := ih.1 leftBody rightBody smallerBody (argument_injective parameter heads)
                have rests := ih.2 parameters leftRest rightRest (List.cons.inj aligned).2 smallerRest tails
                cases bodies
                cases rests
                rfl

theorem toPattern_injective (labels : (language.terms.map (·.label)).Nodup)
    {context : List String} {sort : String} :
    Function.Injective (toPattern (language := language) (context := context) (sort := sort)) := by
  intro left right same
  exact ((printInjectiveSized labels (termSize left + 1)).1 left right (Nat.lt_succ_self _) same)

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
