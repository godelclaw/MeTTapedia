import Mettapedia.Logic.HostingStyles.PrimeCandidate.MatchingLimits
import Mettapedia.GSLT.Dedukti.LanguageDefExamples
import Mettapedia.GSLT.LanguageDef.CostInteraction

/-!
# The probe together with a theory of the λΠ-calculus modulo

A second union of the probe with a presented theory, after the universal
Turing theory.  `probeWithLambdaPi names rules` has the sorts, the
constructors and the rewrites of the probe and of `dkLanguage names rules`:
beta with its substitution, the six congruences, and the declared rules.
Here the rules are rewrites of the presentation, not data in a term: each
theory has its own union.

The statements are made once, for every language that carries the calculus
apart from what else it has (`CarriesLambdaPi`): the language of the theory
itself (`dkLanguage_carries`), the union with the probe
(`probeWithLambdaPi_carries`), and the union with any language whose static
equivalence is that of quotation and dropping and which shares no sort and no
redex with the calculus (`withLambdaPi_carries`).

* **Under every evaluator of the premises such a language hosts the theory,
  on the terms of each scope** (`lambdaPiMap_hosting`,
  `CarriesLambdaPi.hostOf_scopes`).  The source is the theory that
  `dkLanguage names rules` hosts by itself (`encodedRewriting`), read by the
  same encoding; one step of the theory is one step of the language
  (`lambdaPi_steps`).  The rewrites of the calculus carry no premise but
  congruence, and the other rewrites match no encoding, so the evaluator is
  not consulted (`step_encode_iff_of_rewrites`,
  `language_rewrites_match_no_encoding`).
* The statics of the union.  Its static equivalence is that of quotation and
  dropping (`withLambdaPi_quoteDropOnly`).  The constructors of the sorts of
  the calculus are those of `dkLanguage names rules` and take arguments of
  those sorts (`SortsFrom`, `withLambdaPi_lfSorts_from`).
  So a term of the union at such a sort is a term of `dkLanguage names rules`
  (`hasType_of_sortsFrom`, `CarriesLambdaPi.encodedAt_iff`), it contains no
  quotation, and the static equivalence at those sorts is identity
  (`CarriesLambdaPi.termSetoid_iff`).
* Under every evaluator a language that carries the calculus has reductions
  of every length and no rank (`CarriesLambdaPi.not_rank`): beta alone gives
  them.
* With all its contexts the union is no host of the theories given by a
  table (`QuoteDropOnly.not_hostOf_tabular_contexts`): its contexts use each
  hole once.
* Three unions pass the declaration gate here: with the pure calculus
  (`pureUnion_validate`), with the calculus with a choice between two results
  (`choiceUnion_validate`), where a declared rule fires under every evaluator
  (`choiceUnion_branches`), and with the theory of an encoding of
  higher-order logic (`holUnion_validate`).
* **The extended probe under the matching evaluator hosts none of these
  theories** (`matching_not_hostedBy_encodedRewriting`): each of them
  branches without bound along one reduction, at the empty scope
  (`encodedRewriting_unboundedBranching`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory RootStep wellScoped_of_test withChoice chooseLeft chooseRight chooseName)
open Mettapedia.GSLT.Dedukti.Language
open Mettapedia.GSLT.Dedukti.TwoRoutes (holTheory termArrow termOf arr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_syntactic)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

variable {base : BasePremiseEvaluator} {theory : Theory} {names : List String}
  {rules : List Dedukti.RewriteRule}

/-! ## Steps on encodings, in a language with more rewrites -/

/-- **Rewrites that match no encoding add no step from an encoding.**  In a
language whose rewrites are those of `dkLanguage names rules` and others
whose left sides match no encoding, a step from the encoding of a term is the
encoding of a step of the theory. -/
theorem stepAt_encode_sound_of_rewrites {lang : LanguageDef} {others : List RewriteRule}
    (rewrites : lang.rewrites = others ++ (dkLanguage names rules).rewrites)
    (apart : ∀ rule ∈ others, ∀ term : LF.Term, matchPattern rule.left (encode term) = [])
    (presents : Presents theory rules) :
    ∀ (fuel : Nat) {source : LF.Term} {target : Pattern},
      StepAt base lang fuel (encode source) target →
        ∃ next, target = encode next ∧ Dedukti.Step theory source next := by
  intro fuel
  induction fuel with
  | zero => intro source target step; cases step
  | succ fuel ih =>
      intro source target step
      cases step with
      | rule member matched premises targetEq =>
          rw [matchPatternForRule_eq_syntactic] at matched
          rw [applyBindingsForRule_eq_syntactic] at targetEq
          rw [rewrites] at member
          rcases List.mem_append.mp member with other | own
          · rw [apart _ other source] at matched
            cases matched
          · rcases List.mem_append.mp own with fixed | declared
            · simp only [fixedRules, List.mem_cons, List.not_mem_nil, or_false] at fixed
              rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl
              · obtain ⟨domain, body, argument, rfl, rfl⟩ := mem_matchPattern_betaLeft matched
                cases premises
                exact ⟨_, by rw [← targetEq, apply_betaRule],
                  Dedukti.Step.root (.beta domain body argument)⟩
              · obtain ⟨function, argument, rfl, rfl⟩ := mem_matchPattern_appLeft matched
                obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
                simp [applyBindings] at inner
                obtain ⟨next, rfl, innerStep⟩ := ih inner
                simp [mergeBindings] at merged
                subst merged
                exact ⟨.app next argument, by rw [← targetEq, apply_appFunctionRule]; rfl,
                  innerStep.plug (.appFunction .hole argument)⟩
              · obtain ⟨function, argument, rfl, rfl⟩ := mem_matchPattern_appLeft matched
                obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
                simp [applyBindings] at inner
                obtain ⟨next, rfl, innerStep⟩ := ih inner
                simp [mergeBindings] at merged
                subst merged
                exact ⟨.app function next, by rw [← targetEq, apply_appArgumentRule]; rfl,
                  innerStep.plug (.appArgument function .hole)⟩
              · obtain ⟨domain, body, rfl, rfl⟩ := mem_matchPattern_piLeft matched
                obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
                simp [applyBindings] at inner
                obtain ⟨next, rfl, innerStep⟩ := ih inner
                simp [mergeBindings] at merged
                subst merged
                exact ⟨.pi next body, by rw [← targetEq, apply_piDomainRule]; rfl,
                  innerStep.plug (.piDomain .hole body)⟩
              · obtain ⟨domain, body, rfl, rfl⟩ := mem_matchPattern_piLeft matched
                obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
                simp [applyBindings] at inner
                obtain ⟨next, rfl, innerStep⟩ := ih inner
                simp [mergeBindings] at merged
                subst merged
                exact ⟨.pi domain next, by rw [← targetEq, apply_piBodyRule]; rfl,
                  innerStep.plug (.piBody domain .hole)⟩
              · obtain ⟨domain, body, rfl, rfl⟩ := mem_matchPattern_lamLeft matched
                obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
                simp [applyBindings] at inner
                obtain ⟨next, rfl, innerStep⟩ := ih inner
                simp [mergeBindings] at merged
                subst merged
                exact ⟨.lam next body, by rw [← targetEq, apply_lamDomainRule]; rfl,
                  innerStep.plug (.lamDomain .hole body)⟩
              · obtain ⟨domain, body, rfl, rfl⟩ := mem_matchPattern_lamLeft matched
                obtain ⟨candidate, inner, merged⟩ := premisesAt_congruence_inv premises
                simp [applyBindings] at inner
                obtain ⟨next, rfl, innerStep⟩ := ih inner
                simp [mergeBindings] at merged
                subst merged
                exact ⟨.lam domain next, by rw [← targetEq, apply_lamBodyRule]; rfl,
                  innerStep.plug (.lamBody domain .hole)⟩
            · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp declared
              have ruleMember : rules[index] ∈ rules := List.getElem_mem bound
              cases premises
              obtain ⟨assignment, rfl, applied⟩ :=
                declared_root_sound (presents.leftAlgebraic _ ruleMember)
                  (presents.rightDetermined _ ruleMember) matched
              exact ⟨_, by rw [← targetEq]; exact applied,
                Dedukti.Step.root (.rule assignment ((presents.rule_iff _).mpr ruleMember))⟩

/-- **A language with the rewrites of `dkLanguage names rules` and others
that match no encoding steps on encodings as the theory does**, under every
evaluator of its premises. -/
theorem step_encode_iff_of_rewrites {lang : LanguageDef} {others : List RewriteRule}
    (rewrites : lang.rewrites = others ++ (dkLanguage names rules).rewrites)
    (apart : ∀ rule ∈ others, ∀ term : LF.Term, matchPattern rule.left (encode term) = [])
    (presents : Presents theory rules) {source : LF.Term} {target : Pattern} :
    Step base lang (encode source) target ↔
      ∃ next, target = encode next ∧ Dedukti.Step theory source next := by
  constructor
  · rintro ⟨fuel, step⟩
    exact stepAt_encode_sound_of_rewrites rewrites apart presents fuel step
  · rintro ⟨next, rfl, step⟩
    obtain ⟨fuel, bounded⟩ :=
      stepAt_encode_complete (base := silentEvaluator) (names := names) presents step
    exact ⟨fuel, StepAt.transport
      (fun rule member => by rw [rewrites]; exact List.mem_append_right others member)
      (fun _ _ _ _ _ _ answered => absurd answered List.not_mem_nil) bounded⟩

/-! ## The union -/

/-- **A language together with the language of a theory of the λΠ-calculus
modulo**: the sorts, the constructors and the rewrites of both, and the
equations of the first. -/
def withLambdaPi (first : LanguageDef) (names : List String)
    (rules : List Dedukti.RewriteRule) : LanguageDef :=
  { first with
    name := first.name ++ "-with-lambda-pi-modulo"
    types := first.types ++ (dkLanguage names rules).types
    terms := first.terms ++ (dkLanguage names rules).terms
    rewrites := first.rewrites ++ (dkLanguage names rules).rewrites }

/-- **The probe together with the language of a theory of the λΠ-calculus
modulo.** -/
def probeWithLambdaPi (names : List String) (rules : List Dedukti.RewriteRule) : LanguageDef :=
  withLambdaPi language names rules

/-- The encoding of a term is a bound variable or an application of a
constructor of the calculus. -/
theorem encode_shape (term : LF.Term) :
    (∃ index, encode term = .bvar index) ∨
      ∃ label arguments, encode term = .apply label arguments ∧
        label ∈ ["Srt", "Con", "Pi", "Lam", "App"] := by
  cases term with
  | var index => exact .inl ⟨index, rfl⟩
  | srt sort => cases sort <;> exact .inr ⟨_, _, rfl, by decide⟩
  | con symbol => exact .inr ⟨_, _, rfl, by decide⟩
  | pi domain body => exact .inr ⟨_, _, rfl, by decide⟩
  | lam domain body => exact .inr ⟨_, _, rfl, by decide⟩
  | app function argument => exact .inr ⟨_, _, rfl, by decide⟩

/-- An application of a constructor that is none of the calculus matches no
encoding. -/
theorem matchPattern_encode_of_label {label : String} (parameters : List Pattern)
    (outside : label ∉ ["Srt", "Con", "Pi", "Lam", "App"]) (term : LF.Term) :
    matchPattern (.apply label parameters) (encode term) = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun bindings matched => ?_
  obtain ⟨arguments, shape, -⟩ := eq_apply_of_matched matched
  rcases encode_shape term with ⟨index, isVariable⟩ | ⟨found, others, isApply, listed⟩
  · rw [isVariable] at shape
    cases shape
  · rw [isApply] at shape
    injection shape with sameLabel
    exact outside (sameLabel ▸ listed)

/-- **No rewrite of the probe with the run constructor matches an
encoding.** -/
theorem probeWithRun_rewrites_match_no_encoding :
    ∀ rule ∈ probeWithRun.rewrites, ∀ term : LF.Term,
      matchPattern rule.left (encode term) = [] := by
  intro rule member term
  rw [probeWithRun_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact matchPattern_encode_of_label _ (by decide) term

/-- **No rewrite of the probe matches an encoding.** -/
theorem language_rewrites_match_no_encoding :
    ∀ rule ∈ language.rewrites, ∀ term : LF.Term, matchPattern rule.left (encode term) = [] :=
  fun rule member => probeWithRun_rewrites_match_no_encoding rule
    (List.mem_append_left [runRewrite] member)

/-! ## The constructors of the calculus -/

theorem nameLabel_ne_quote (symbol : String) : nameLabel symbol ≠ "prime-quote" := by
  intro same
  have lists := congrArg String.toList same
  simp [nameLabel, String.toList_append] at lists

theorem nameLabel_ne_drop (symbol : String) : nameLabel symbol ≠ "prime-drop" := by
  intro same
  have lists := congrArg String.toList same
  simp [nameLabel, String.toList_append] at lists

/-- No constructor of the calculus is quotation or dropping. -/
theorem dkLanguage_label_apart {rule : GrammarRule}
    (member : rule ∈ (dkLanguage names rules).terms) :
    rule.label ≠ "prime-quote" ∧ rule.label ≠ "prime-drop" := by
  rcases mem_dkLanguage_terms member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨symbol, -, rfl⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact ⟨nameLabel_ne_quote symbol, nameLabel_ne_drop symbol⟩

/-- Every constructor of the calculus takes arguments of the sorts of the
calculus. -/
theorem dkLanguage_parameters_lf {rule : GrammarRule}
    (member : rule ∈ (dkLanguage names rules).terms) :
    ∀ parameter ∈ rule.params, ∀ expected ∈ parameterType? parameter,
      resultIn lfSorts expected = true := by
  rcases mem_dkLanguage_terms member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨symbol, -, rfl⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro parameter inParams
    exact absurd inParams List.not_mem_nil

/-- No constructor of the calculus takes a collection. -/
theorem dkLanguage_no_collection {rule : GrammarRule}
    (member : rule ∈ (dkLanguage names rules).terms) (kind : CollType) :
    (rule.params.any fun parameter => TypeExpr.mentionsCollection kind parameter.typeExpr) =
      false := by
  rcases mem_dkLanguage_terms member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨symbol, -, rfl⟩
  · cases kind <;> decide
  · cases kind <;> decide
  · cases kind <;> decide
  · cases kind <;> decide
  · cases kind <;> decide
  · cases kind <;> decide
  · cases kind <;> decide
  · cases kind <;> decide
  · rfl

/-- No constructor of the probe is of a sort of the calculus. -/
theorem language_category_not_lf : ∀ rule ∈ language.terms, rule.category ∉ lfSorts := by
  decide

/-! ## The statics of a union -/

/-- **The static equivalence of a union is that of quotation and dropping
when that of its first language is**: the calculus brings no equation and no
collection. -/
theorem withLambdaPi_quoteDropOnly {first : LanguageDef} (only : QuoteDropOnly first) :
    QuoteDropOnly (withLambdaPi first names rules) where
  equations := only.equations
  noBags := List.any_eq_false.mpr fun rule member => by
    rcases List.mem_append.mp member with inFirst | inCalculus
    · exact List.any_eq_false.mp only.noBags rule inFirst
    · rw [dkLanguage_no_collection inCalculus]
      exact Bool.false_ne_true
  noSets := List.any_eq_false.mpr fun rule member => by
    rcases List.mem_append.mp member with inFirst | inCalculus
    · exact List.any_eq_false.mp only.noSets rule inFirst
    · rw [dkLanguage_no_collection inCalculus]
      exact Bool.false_ne_true
  noAlgebra := List.any_eq_false.mpr fun rule member => by
    rcases List.mem_append.mp member with inFirst | inCalculus
    · exact List.any_eq_false.mp only.noAlgebra rule inFirst
    · rw [(dkLanguage_terms_plain rule inCalculus).1]
      exact Bool.false_ne_true

theorem withLambdaPi_quoteDropSorted {first : LanguageDef} (sorted : QuoteDropSorted first) :
    QuoteDropSorted (withLambdaPi first names rules) where
  quote := fun rule member label => by
    rcases List.mem_append.mp member with inFirst | inCalculus
    · exact sorted.quote rule inFirst label
    · exact absurd label (dkLanguage_label_apart inCalculus).1
  drop := fun rule member label => by
    rcases List.mem_append.mp member with inFirst | inCalculus
    · exact sorted.drop rule inFirst label
    · exact absurd label (dkLanguage_label_apart inCalculus).2

theorem probeWithLambdaPi_quoteDropOnly : QuoteDropOnly (probeWithLambdaPi names rules) :=
  withLambdaPi_quoteDropOnly language_quoteDropOnly

/-! ## Sorts whose constructors are those of a smaller language -/

/-- **The constructors of some sorts of a language are those of a smaller
language, and take arguments of those sorts.** -/
def SortsFrom (lang smaller : LanguageDef) (sorts : List String) : Prop :=
  ∀ rule ∈ lang.terms, rule.category ∈ sorts →
    rule ∈ smaller.terms ∧
      ∀ parameter ∈ rule.params, ∀ expected ∈ parameterType? parameter,
        resultIn sorts expected = true

/-- **Positive**: the sorts of the calculus, in a union with a language that
has no constructor of those sorts. -/
theorem withLambdaPi_lfSorts_from {first : LanguageDef}
    (categories : ∀ rule ∈ first.terms, rule.category ∉ lfSorts) :
    SortsFrom (withLambdaPi first names rules) (dkLanguage names rules) lfSorts := by
  intro rule member category
  rcases List.mem_append.mp member with inFirst | inCalculus
  · exact absurd category (categories rule inFirst)
  · exact ⟨inCalculus, dkLanguage_parameters_lf inCalculus⟩

/-- The constructors of the calculus are of its sorts. -/
theorem dkLanguage_category_lf {rule : GrammarRule}
    (member : rule ∈ (dkLanguage names rules).terms) : rule.category ∈ lfSorts := by
  rcases mem_dkLanguage_terms member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨symbol, -, rfl⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · show "LFName" ∈ lfSorts
    decide

/-- **Negative**: the sort of atoms, whose constructors are those of the
probe. -/
theorem probeWithLambdaPi_atom_not_from :
    ¬ SortsFrom (probeWithLambdaPi names rules) (dkLanguage names rules) ["Atom"] := by
  intro closed
  have declared : dropConstructor ∈ (probeWithLambdaPi names rules).terms :=
    List.mem_append_left _ (by decide)
  have inCalculus := (closed dropConstructor declared (by decide)).1
  have category := dkLanguage_category_lf inCalculus
  revert category
  decide

/-- Sorts whose constructors are those of a language without quotation are
apart from quotation. -/
theorem SortsFrom.apart {lang smaller : LanguageDef} {sorts : List String}
    (closed : SortsFrom lang smaller sorts)
    (unquoted : ∀ rule ∈ smaller.terms, rule.label ≠ "prime-quote") :
    ApartFromQuotation lang sorts :=
  fun rule member category =>
    ⟨unquoted rule (closed rule member category).1, (closed rule member category).2⟩

mutual
  /-- **A term of sorts whose constructors are those of a smaller language is
  a term of the smaller language.** -/
  theorem hasType_of_sortsFrom {lang smaller : LanguageDef} {sorts : List String}
      (closed : SortsFrom lang smaller sorts) {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr} (typed : HasType lang free bound pattern type)
      (inSorts : resultIn sorts type = true) (object : isObjectPattern pattern = true) :
      HasType smaller free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | @constructor _ rule arguments member notBare argumentsTyped =>
        have category : rule.category ∈ sorts := by simpa [resultIn] using inSorts
        obtain ⟨inSmaller, parameters⟩ := closed rule member category
        exact .constructor inSmaller notBare
          (arguments_of_sortsFrom closed argumentsTyped parameters
            (by simpa [isObjectPattern] using object))
    | lambda bodyTyped =>
        exact .lambda (hasType_of_sortsFrom closed bodyTyped (by simpa [resultIn] using inSorts)
          (by simpa [isObjectPattern] using object))
    | multiLambda bodyTyped =>
        exact .multiLambda
          (hasType_of_sortsFrom closed bodyTyped (by simpa [resultIn] using inSorts)
            (by simpa [isObjectPattern] using object))
    | subst _ _ => simp [isObjectPattern] at object
    | collection elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        exact .collection
          (elements_of_sortsFrom closed elementsTyped (by simpa [resultIn] using inSorts)
            object.2)
    | @collectionConstructor _ rule parameterName kind elements rest elementType member shape
        elementsTyped =>
        have category : rule.category ∈ sorts := by simpa [resultIn] using inSorts
        obtain ⟨inSmaller, parameters⟩ := closed rule member category
        have fullShape := ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2
        have element := parameters (.simple parameterName (.collection kind elementType))
          (by rw [fullShape]; exact List.mem_singleton.mpr rfl) (.collection kind elementType) rfl
        simp only [isObjectPattern, Bool.and_eq_true] at object
        exact .collectionConstructor inSmaller shape
          (elements_of_sortsFrom closed elementsTyped (by simpa [resultIn] using element)
            object.2)

  theorem arguments_of_sortsFrom {lang smaller : LanguageDef} {sorts : List String}
      (closed : SortsFrom lang smaller sorts) {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes lang free bound arguments parameters)
      (inSorts : ∀ parameter ∈ parameters, ∀ expected ∈ parameterType? parameter,
        resultIn sorts expected = true)
      (object : isObjectPatternList arguments = true) :
      ArgumentsHaveTypes smaller free bound arguments parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation expectedType argumentTyped argumentsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        exact .cons representation expectedType
          (hasType_of_sortsFrom closed argumentTyped
            (inSorts _ (List.mem_cons_self ..) _ expectedType) object.1)
          (arguments_of_sortsFrom closed argumentsTyped
            (fun parameter member => inSorts parameter (List.mem_cons_of_mem _ member)) object.2)

  theorem elements_of_sortsFrom {lang smaller : LanguageDef} {sorts : List String}
      (closed : SortsFrom lang smaller sorts) {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType lang free bound elements elementType)
      (inSorts : resultIn sorts elementType = true)
      (object : isObjectPatternList elements = true) :
      ElementsHaveType smaller free bound elements elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        exact .cons (hasType_of_sortsFrom closed elementTyped inSorts object.1)
          (elements_of_sortsFrom closed elementsTyped inSorts object.2)
end

/-- The sort of the terms of the calculus is one of its sorts. -/
theorem lfTerm_resultIn : resultIn lfSorts (.base "LFTerm") = true := by decide

/-! ## Languages that carry the calculus -/

/-- **A language carries the language of a theory of the λΠ-calculus modulo
apart from what else it has**: it has the constructors of the calculus and no
other constructor of its sorts; its rewrites are those of the calculus and
others that match no encoding; and at the sort of the terms of the calculus
its static equivalence is identity. -/
structure CarriesLambdaPi (lang : LanguageDef) (names : List String)
    (rules : List Dedukti.RewriteRule) : Prop where
  includes : ∀ rule ∈ (dkLanguage names rules).terms, rule ∈ lang.terms
  sorts : SortsFrom lang (dkLanguage names rules) lfSorts
  rewrites : ∃ others : List RewriteRule,
    lang.rewrites = others ++ (dkLanguage names rules).rewrites ∧
      ∀ rule ∈ others, ∀ term : LF.Term, matchPattern rule.left (encode term) = []
  discrete : ∀ {base : BasePremiseEvaluator} {depth : Nat}
    (first second : Contexts.Term lang (termInterface depth)),
      (termSetoid base lang (termInterface depth)).r first second → first = second

/-- A language whose static equivalence is that of quotation and dropping
carries the calculus when it has its constructors, no other constructor of
its sorts, and no other rewrite that matches an encoding. -/
theorem CarriesLambdaPi.of_quoteDrop {lang : LanguageDef} (only : QuoteDropOnly lang)
    (sorted : QuoteDropSorted lang)
    (includes : ∀ rule ∈ (dkLanguage names rules).terms, rule ∈ lang.terms)
    (sorts : SortsFrom lang (dkLanguage names rules) lfSorts)
    (rewrites : ∃ others : List RewriteRule,
      lang.rewrites = others ++ (dkLanguage names rules).rewrites ∧
        ∀ rule ∈ others, ∀ term : LF.Term, matchPattern rule.left (encode term) = []) :
    CarriesLambdaPi lang names rules where
  includes := includes
  sorts := sorts
  rewrites := rewrites
  discrete := fun first second related => by
    have apart : ApartFromQuotation lang lfSorts :=
      sorts.apart fun _ member => (dkLanguage_label_apart member).1
    have same := (only.termSetoid_iff sorted).mp related
    rw [contract_of_hasType apart first.2.1 lfTerm_resultIn first.2.2.2.1,
      contract_of_hasType apart second.2.1 lfTerm_resultIn second.2.2.2.1] at same
    exact Subtype.ext same

/-- **Positive**: the language of the theory itself. -/
theorem dkLanguage_carries (names : List String) (rules : List Dedukti.RewriteRule) :
    CarriesLambdaPi (dkLanguage names rules) names rules where
  includes := fun _ member => member
  sorts := fun _ member _ => ⟨member, dkLanguage_parameters_lf member⟩
  rewrites := ⟨[], rfl, fun _ member => absurd member List.not_mem_nil⟩
  discrete := fun first second related => (dk_termSetoid_iff first second).mp related

/-- **Positive**: a union with a language whose static equivalence is that of
quotation and dropping, which has no constructor of the sorts of the calculus
and no rewrite that matches an encoding. -/
theorem withLambdaPi_carries {first : LanguageDef} (only : QuoteDropOnly first)
    (sorted : QuoteDropSorted first)
    (categories : ∀ rule ∈ first.terms, rule.category ∉ lfSorts)
    (apart : ∀ rule ∈ first.rewrites, ∀ term : LF.Term,
      matchPattern rule.left (encode term) = []) :
    CarriesLambdaPi (withLambdaPi first names rules) names rules :=
  .of_quoteDrop (withLambdaPi_quoteDropOnly only) (withLambdaPi_quoteDropSorted sorted)
    (fun _ member => List.mem_append_right first.terms member)
    (withLambdaPi_lfSorts_from categories) ⟨first.rewrites, rfl, apart⟩

/-- **Positive**: the probe together with the language of the theory. -/
theorem probeWithLambdaPi_carries (names : List String) (rules : List Dedukti.RewriteRule) :
    CarriesLambdaPi (probeWithLambdaPi names rules) names rules :=
  withLambdaPi_carries language_quoteDropOnly language_quoteDropSorted language_category_not_lf
    language_rewrites_match_no_encoding

/-- **Negative**: the probe alone, which has no constructor of the calculus. -/
theorem language_not_carries : ¬ CarriesLambdaPi language names rules := by
  intro carries
  have declared := carries.includes appRule (lfRule_mem (by simp [lfTermRules]))
  revert declared
  decide

namespace CarriesLambdaPi

variable {lang : LanguageDef}

/-- **The steps of such a language on encodings are the steps of the
theory**, under every evaluator of the premises. -/
theorem step_encode_iff (carries : CarriesLambdaPi lang names rules)
    (presents : Presents theory rules) {source : LF.Term} {target : Pattern} :
    Step base lang (encode source) target ↔
      ∃ next, target = encode next ∧ Dedukti.Step theory source next := by
  obtain ⟨others, rewrites, apart⟩ := carries.rewrites
  exact step_encode_iff_of_rewrites rewrites apart presents

/-- **A term is encoded in such a language exactly when it is encoded in the
language of the theory**: at a scope, the two languages have the same terms
of the calculus. -/
theorem encodedAt_iff (carries : CarriesLambdaPi lang names rules) {depth : Nat}
    {term : LF.Term} :
    EncodedAt lang depth term ↔ EncodedAt (dkLanguage names rules) depth term :=
  ⟨fun encoded =>
      ⟨hasType_of_sortsFrom carries.sorts encoded.1 lfTerm_resultIn encoded.2.2.1,
        encoded.2.1, encoded.2.2.1, encoded.2.2.2⟩,
    fun encoded =>
      ⟨encoded.1.weakenTerms carries.includes, encoded.2.1, encoded.2.2.1, encoded.2.2.2⟩⟩

/-- **At the sort of the terms of the calculus the static equivalence is
identity.** -/
theorem termSetoid_iff (carries : CarriesLambdaPi lang names rules) {depth : Nat}
    (first second : Contexts.Term lang (termInterface depth)) :
    (termSetoid base lang (termInterface depth)).r first second ↔ first = second := by
  constructor
  · exact carries.discrete first second
  · rintro rfl
    exact Relation.EqvGen.refl _

/-- **A transition there is a step of the language.** -/
theorem termStep_iff (carries : CarriesLambdaPi lang names rules) {depth : Nat}
    (source target : Contexts.Term lang (termInterface depth)) :
    TermStep base lang source target ↔ Step base lang source.1 target.1 := by
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    obtain rfl := carries.discrete _ _ before
    obtain rfl := carries.discrete _ _ after
    exact step
  · intro step
    exact ⟨source, target, Relation.EqvGen.refl _, step, Relation.EqvGen.refl _⟩

end CarriesLambdaPi

/-! ## The map, and the sentence -/

/-- **The encoding, as a map into a language that carries the calculus**:
from the theory on the terms of one scope, as `dkLanguage names rules` has
them. -/
def lambdaPiMap {lang : LanguageDef} (base : BasePremiseEvaluator) (theory : Theory)
    (carries : CarriesLambdaPi lang names rules) (valid : lang.validate = []) (depth : Nat) :
    ContextMap (encodedRewriting theory (dkLanguage names rules) depth).termsAlone
      (contextTheory base ⟨lang, valid⟩) :=
  ContextMap.ofTerms (source := encodedRewriting theory (dkLanguage names rules) depth)
    (target := contextTheory base ⟨lang, valid⟩) (termInterface depth)
    (fun term => ⟨encode term.1, carries.encodedAt_iff.mpr term.2⟩)
    (fun same => by subst same; exact Relation.EqvGen.refl _)

/-- **Under every evaluator the encoding into a language that carries the
calculus is hosting**: it identifies no two terms, and the transitions of the
image of a term are the images of its steps. -/
theorem lambdaPiMap_hosting {lang : LanguageDef} (presents : Presents theory rules)
    (carries : CarriesLambdaPi lang names rules) (valid : lang.validate = [])
    (base : BasePremiseEvaluator) (depth : Nat) :
    (lambdaPiMap base theory carries valid depth).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff
    (source := encodedRewriting theory (dkLanguage names rules) depth)
    (target := contextTheory base ⟨lang, valid⟩) (termInterface depth)
    (fun term => ⟨encode term.1, carries.encodedAt_iff.mpr term.2⟩)
    (fun same => by subst same; exact Relation.EqvGen.refl _)).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    have same := (carries.termSetoid_iff _ _).mp related
    exact Subtype.ext (encode_injective (congrArg Subtype.val same))
  · intro first next step
    exact (carries.termStep_iff _ _).mpr ((carries.step_encode_iff presents).mpr ⟨_, rfl, step⟩)
  · intro first next step
    obtain ⟨target, targetEq, sourceStep⟩ :=
      (carries.step_encode_iff presents).mp ((carries.termStep_iff _ _).mp step)
    refine ⟨⟨target, ?_⟩, sourceStep, ?_⟩
    · have sorted := next.2
      rw [targetEq] at sorted
      exact carries.encodedAt_iff.mp sorted
    · exact (carries.termSetoid_iff _ _).mpr (Subtype.ext targetEq)

/-- The probe together with the language of a theory, when it passes the
declaration gate, as a presentation. -/
def lambdaPiPresentation (names : List String) (rules : List Dedukti.RewriteRule)
    (valid : (probeWithLambdaPi names rules).validate = []) : ValidatedLanguageDef :=
  ⟨probeWithLambdaPi names rules, valid⟩

/-- **The scopes of a theory**: the theory on the terms of
`dkLanguage names rules` beneath each number of binders. -/
def ScopesOf (theory : Theory) (names : List String) (rules : List Dedukti.RewriteRule)
    (source : ContextTheory.{0}) : Prop :=
  ∃ depth : Nat, source = (encodedRewriting theory (dkLanguage names rules) depth).termsAlone

/-- **Positive**: the closed terms. -/
theorem closed_scopesOf (theory : Theory) (names : List String)
    (rules : List Dedukti.RewriteRule) :
    ScopesOf theory names rules (encodedRewriting theory (dkLanguage names rules) 0).termsAlone :=
  ⟨0, rfl⟩

/-- **Negative**: a generated context theory, which has many interfaces. -/
theorem contextTheory_not_scopesOf (base : BasePremiseEvaluator)
    (presentation : ValidatedLanguageDef) :
    ¬ ScopesOf theory names rules (contextTheory base presentation) := by
  rintro ⟨depth, same⟩
  have interfaces : Contexts.Interface = PUnit := congrArg ContextTheory.Interface same
  have distinct : (⟨.base "a", []⟩ : Contexts.Interface) ≠ ⟨.base "b", []⟩ := by simp
  exact distinct ((Equiv.cast interfaces).injective (Subsingleton.elim _ _))

theorem CarriesLambdaPi.hostsEvery {lang : LanguageDef}
    (carries : CarriesLambdaPi lang names rules) (presents : Presents theory rules)
    (valid : lang.validate = []) (base : BasePremiseEvaluator) :
    HostsEvery (contextTheory base ⟨lang, valid⟩) (ScopesOf theory names rules) := by
  rintro source ⟨depth, rfl⟩
  exact ⟨lambdaPiMap base theory carries valid depth,
    lambdaPiMap_hosting presents carries valid base depth⟩

/-- **The sentence for a language that carries a theory of the λΠ-calculus
modulo**: under every evaluator of its premises, it is a host of the scopes
of the theory, on terms. -/
theorem CarriesLambdaPi.hostOf_scopes {lang : LanguageDef}
    (carries : CarriesLambdaPi lang names rules) (presents : Presents theory rules)
    (valid : lang.validate = []) (base : BasePremiseEvaluator) :
    HostOf (contextTheory base ⟨lang, valid⟩) (ScopesOf theory names rules) .terms .hosting :=
  HostOf.terms (hostOf_contexts_hosting_iff.mpr (carries.hostsEvery presents valid base))

/-- **One step of the theory is one step of the language**: a reduction of
`count` steps of the theory is a reduction of `count` steps of the language,
under every evaluator. -/
theorem lambdaPi_steps {lang : LanguageDef} (presents : Presents theory rules)
    (carries : CarriesLambdaPi lang names rules) (valid : lang.validate = [])
    (base : BasePremiseEvaluator) {depth count : Nat}
    {first final : (encodedRewriting theory (dkLanguage names rules) depth).Term}
    (steps : (encodedRewriting theory (dkLanguage names rules) depth).termsAlone.Steps
      (interface := PUnit.unit) count first final) :
    (contextTheory base ⟨lang, valid⟩).Steps count
      ((lambdaPiMap base theory carries valid depth).term (origin := PUnit.unit) first)
      ((lambdaPiMap base theory carries valid depth).term (origin := PUnit.unit) final) :=
  (lambdaPiMap base theory carries valid depth).steps_of_preserves
    (lambdaPiMap_hosting presents carries valid base depth).preserves steps

/-! ## Reductions of every length -/

theorem grown_wellScoped : ∀ count, LF.WellScoped 0 (grown count)
  | 0 => wellScoped_of_test _ 0 rfl
  | count + 1 => .app (grown_wellScoped count) (wellScoped_of_test _ 0 rfl)

theorem grown_constants : ∀ count, constants (grown count) = []
  | 0 => by decide
  | count + 1 => by
      have rest := grown_constants count
      simp [grown, constants, rest, selfIdentity, identityTerm]

theorem contractedAt_wellScoped : ∀ count place, LF.WellScoped 0 (contractedAt count place)
  | 0, _ => grown_wellScoped 0
  | count + 1, place => by
      rw [contractedAt]
      split
      · exact .app (grown_wellScoped count) (wellScoped_of_test _ 0 rfl)
      · exact .app (contractedAt_wellScoped count place) (wellScoped_of_test _ 0 rfl)

theorem contractedAt_constants : ∀ count place, constants (contractedAt count place) = []
  | 0, _ => grown_constants 0
  | count + 1, place => by
      have whole := grown_constants count
      have rest := contractedAt_constants count place
      rw [contractedAt]
      split <;> simp [constants, whole, rest, selfIdentity, identityTerm]

/-- The terms of the growing sequence, as terms of a theory at the empty
scope: they are closed and mention no constant. -/
def grownTerm (theory : Theory) (names : List String) (rules : List Dedukti.RewriteRule)
    (count : Nat) : (encodedRewriting theory (dkLanguage names rules) 0).Term :=
  ⟨grown count, encode_encodedAt (grown_wellScoped count) (by
    rw [grown_constants]
    intro symbol member
    cases member)⟩

/-- The terms with one collected redex contracted, at the empty scope. -/
def contractedTerm (theory : Theory) (names : List String) (rules : List Dedukti.RewriteRule)
    (count place : Nat) : (encodedRewriting theory (dkLanguage names rules) 0).Term :=
  ⟨contractedAt count place, encode_encodedAt (contractedAt_wellScoped count place) (by
    rw [contractedAt_constants]
    intro symbol member
    cases member)⟩

/-- **Every theory of the λΠ-calculus modulo branches without bound along one
reduction at the empty scope**, whatever its constants and its rules. -/
theorem encodedRewriting_unboundedBranching (theory : Theory) (names : List String)
    (rules : List Dedukti.RewriteRule) :
    UnboundedBranching (encodedRewriting theory (dkLanguage names rules) 0) := by
  refine ⟨grownTerm theory names rules, fun index => grown_step theory index, fun index => ?_⟩
  have length : ((List.range index).map (contractedTerm theory names rules index)).length =
      index := by
    rw [List.length_map, List.length_range]
  refine ⟨(List.range index).map (contractedTerm theory names rules index), length, ?_, ?_⟩
  · intro reduct member
    have listed : reduct ∈ (List.range index).map (contractedTerm theory names rules index) :=
      member
    obtain ⟨place, inRange, rfl⟩ := List.mem_map.mp listed
    exact contractedAt_step theory index place (List.mem_range.mp inRange)
  · have distinct : ((List.range index).map (contractedTerm theory names rules index)).Nodup :=
      List.Nodup.map_on (fun first firstMember second secondMember same =>
        contractedAt_injective index first second (List.mem_range.mp firstMember)
          (List.mem_range.mp secondMember) (congrArg Subtype.val same)) List.nodup_range
    exact distinct

/-- **The extended probe under the matching evaluator hosts no theory of the
λΠ-calculus modulo at the empty scope**, on terms. -/
theorem matching_not_hostedBy_encodedRewriting (theory : Theory) (names : List String)
    (rules : List Dedukti.RewriteRule) :
    ¬ HostedBy (encodedRewriting theory (dkLanguage names rules) 0).termsAlone
      matchingCandidate :=
  not_hostedBy_matching_of_unboundedBranching
    (encodedRewriting_unboundedBranching theory names rules)

/-- So it is no host of the scopes of any of them. -/
theorem matchingCandidate_not_hostOf_scopes (theory : Theory) (names : List String)
    (rules : List Dedukti.RewriteRule) :
    ¬ HostOf matchingCandidate (ScopesOf theory names rules) .terms .hosting :=
  fun hosts => matching_not_hostedBy_encodedRewriting theory names rules
    (hosts _ ⟨_, closed_scopesOf theory names rules, PUnit.unit, rfl⟩)

/-- The pure calculus is presented by the empty list of rules. -/
theorem pure_presents : Presents Theory.empty [] where
  undefined := fun _ => rfl
  rule_iff := fun rule => by simp [Theory.empty]
  leftAlgebraic := fun rule member => absurd member List.not_mem_nil
  rightDetermined := fun rule member => absurd member List.not_mem_nil

/-- The terms of the growing sequence, as terms of a language that carries
the calculus. -/
def grownCarriedTerm {lang : LanguageDef} (carries : CarriesLambdaPi lang names rules)
    (count : Nat) : Contexts.Term lang (termInterface 0) :=
  ⟨encode (grown count), carries.encodedAt_iff.mpr (grownTerm Theory.empty names rules count).2⟩

/-- **Beta alone grows the sequence, in every language that carries the
calculus and under every evaluator.** -/
theorem grownCarried_step {lang : LanguageDef} (base : BasePremiseEvaluator)
    (carries : CarriesLambdaPi lang names rules) (count : Nat) :
    TermStep base lang (grownCarriedTerm carries count)
      (grownCarriedTerm carries (count + 1)) := by
  obtain ⟨others, rewrites, -⟩ := carries.rewrites
  obtain ⟨fuel, bounded⟩ := stepAt_encode_complete (base := silentEvaluator) (names := [])
    pure_presents (grown_step Theory.empty count)
  refine (carries.termStep_iff _ _).mpr ⟨fuel, StepAt.transport (fun rule member => ?_)
    (fun _ _ _ _ _ _ answered => absurd answered List.not_mem_nil) bounded⟩
  have fixed : rule ∈ fixedRules := by simpa [dkLanguage] using member
  rw [rewrites]
  exact List.mem_append_right others (List.mem_append_left _ fixed)

theorem grownCarried_steps {lang : LanguageDef} (base : BasePremiseEvaluator)
    (carries : CarriesLambdaPi lang names rules) (valid : lang.validate = []) (count : Nat) :
    ∀ start : Nat, (contextTheory base ⟨lang, valid⟩).Steps count
      (grownCarriedTerm carries start) (grownCarriedTerm carries (start + count)) := by
  induction count with
  | zero => exact fun start => .zero _
  | succ count ih =>
      intro start
      have rest := ih (start + 1)
      rw [Nat.add_right_comm] at rest
      exact .succ (grownCarried_step base carries start) rest

/-- **Under every evaluator, the one that answers nothing included, a
language that carries the calculus has no rank.** -/
theorem CarriesLambdaPi.not_rank {lang : LanguageDef}
    (carries : CarriesLambdaPi lang names rules) (valid : lang.validate = [])
    (base : BasePremiseEvaluator) : IsEmpty (contextTheory base ⟨lang, valid⟩).Rank := by
  refine ⟨fun ranked => ?_⟩
  have bounded := ranked.steps_le
    (grownCarried_steps base carries valid (ranked.rank (grownCarriedTerm carries 0) + 1) 0)
  omega

/-! ## With all contexts -/

/-- **With all its contexts a presentation whose static equivalence is that
of quotation and dropping is no host of the theories given by a table, under
any evaluator**: its contexts use each hole once, while those of the theories
given by a table discard and copy.  This holds of the probe together with a
theory of the λΠ-calculus modulo, where the calculus is a summand. -/
theorem QuoteDropOnly.not_hostOf_tabular_contexts (presentation : ValidatedLanguageDef)
    (only : QuoteDropOnly presentation.language) (base : BasePremiseEvaluator) :
    ¬ HostOf (contextTheory base presentation) TabularTheory .contexts .hosting :=
  fun hosts =>
    let ⟨map, _⟩ := hosts _ pure_tabular
    ((QuoteDropOnly.linearSize presentation only base).isEmpty_contextMap_of_discards
      (rewritingTheory_discards Theory.empty) ⟨(.srt .type : LF.Term)⟩).false map

/-! ## Three unions that pass the declaration gate -/

/-- Unfold the rows of the declaration gate for a rewrite of the probe or the
run rewrite, given the type names, the constructor signatures and the
constructor labels of the language. -/
scoped macro "check_probe_rewrite" typeNames:ident signatures:ident labels:ident : tactic =>
  `(tactic|
    simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.premiseTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      $typeNames:ident, $signatures:ident, $labels:ident,
      MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, needRewrite, evaluationDemandRewrite,
      needReturnRewrite, reflectedDemandRewrite, runRewrite,
      MeTTaZero.queryRequestPattern, MeTTaZero.queryAnswerPattern,
      MeTTaZero.evaluationRequestPattern, MeTTaZero.evaluationAnswerPattern,
      MeTTaZero.metavariable,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt])

/-- The same for a rewrite of the calculus: beta, a congruence, or one of the
declared rules of the examples. -/
scoped macro "check_calculus_rewrite" typeNames:ident signatures:ident labels:ident : tactic =>
  `(tactic|
    simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.premiseTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      $typeNames:ident, $signatures:ident, $labels:ident,
      betaRule, betaLeft, appFunctionRule, appArgumentRule, piDomainRule, piBodyRule,
      lamDomainRule, lamBodyRule, appLeft, piLeft, lamLeft,
      declaredRule, toPattern, metaName_zero, metaName_one, chooseLeft, chooseRight,
      Dedukti.choose, chooseName, termArrow, termOf, arr, encode, nameLabel,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt])

/-! ### The pure calculus -/

/-- **The probe together with the pure calculus**: no constant and no
declared rule; beta and the congruences. -/
def pureUnion : LanguageDef := probeWithLambdaPi [] []

theorem pureUnion_typeNames : pureUnion.typeNames =
    ["Atom", "Space", "Process", "Alternatives", "CandidateName", "CandidateReceipt", "LFSort",
      "LFTerm", "LFName", "LFIndex"] := by
  decide

theorem pureUnion_signatures :
    RewriteValidationCertificate.constructorSignatures pureUnion =
      [("=", 2), ("zero-query", 3), ("zero-query-answer", 1), ("zero-evaluate", 2),
        ("zero-evaluate-answer", 1), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-evaluate-name", 2), ("prime-need", 2), ("prime-need-answer", 2),
        ("prime-need-key", 2), ("prime-request-dependency", 1),
        ("prime-space-atom-dependency", 2), ("prime-capability-dependency", 2),
        ("prime-inert-dependency", 1), ("prime-receipt", 1), ("SortType", 0), ("SortKind", 0),
        ("Srt", 1), ("Con", 1), ("Var", 1), ("Pi", 2), ("Lam", 2), ("App", 2)] := by
  decide

theorem pureUnion_labels :
    RewriteValidationCertificate.constructorLabels pureUnion =
      ["=", "zero-query", "zero-query-answer", "zero-evaluate", "zero-evaluate-answer",
        "prime-unit", "prime-quote", "prime-drop", "prime-evaluate-name", "prime-need",
        "prime-need-answer", "prime-need-key", "prime-request-dependency",
        "prime-space-atom-dependency", "prime-capability-dependency", "prime-inert-dependency",
        "prime-receipt", "SortType", "SortKind", "Srt", "Con", "Var", "Pi", "Lam", "App"] := by
  decide

theorem pureUnion_probe_checked :
    ∀ rewrite ∈ language.rewrites,
      RewriteValidationCertificate.check pureUnion rewrite = true := by
  intro rewrite member
  change rewrite ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, evaluationDemandRewrite,
    needRewrite, needReturnRewrite, reflectedDemandRewrite] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    check_probe_rewrite pureUnion_typeNames pureUnion_signatures pureUnion_labels

theorem pureUnion_calculus_checked :
    ∀ rewrite ∈ (dkLanguage [] []).rewrites,
      RewriteValidationCertificate.check pureUnion rewrite = true := by
  intro rewrite member
  simp only [dkLanguage, fixedRules, List.mapIdx_nil, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    check_calculus_rewrite pureUnion_typeNames pureUnion_signatures pureUnion_labels

/-- **The union with the pure calculus passes the declaration gate.** -/
theorem pureUnion_validate : pureUnion.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro equation member
    exact LanguageDef.validateEquation_eq_nil_of_plainEquationOk
      (List.all_eq_true.mp
        (by decide +kernel :
          pureUnion.equations.all (LanguageDef.plainEquationOk pureUnion) = true)
        equation member)
  · intro rewrite member
    refine RewriteValidationCertificate.validateRewrite_eq_nil_of_check (by decide +kernel) ?_
    rcases List.mem_append.mp member with inProbe | inCalculus
    · exact pureUnion_probe_checked rewrite inProbe
    · exact pureUnion_calculus_checked rewrite inCalculus

/-- **Positive**: under every evaluator, the union with the pure calculus is
a host of the scopes of the pure calculus, on terms.  Its only rewrites
beside those of the probe are beta and the congruences. -/
theorem pureUnion_hostOf_scopes (base : BasePremiseEvaluator) :
    HostOf (contextTheory base (lambdaPiPresentation [] [] pureUnion_validate))
      (ScopesOf Theory.empty [] []) .terms .hosting :=
  (probeWithLambdaPi_carries [] []).hostOf_scopes pure_presents pureUnion_validate base

/-! ### The calculus with a choice between two results -/

/-- **The probe together with the calculus with choice**: one constant and
the two rules `choose x y ⟶ x` and `choose x y ⟶ y`. -/
def choiceUnion : LanguageDef := probeWithLambdaPi [chooseName] [chooseLeft, chooseRight]

theorem choiceUnion_typeNames : choiceUnion.typeNames =
    ["Atom", "Space", "Process", "Alternatives", "CandidateName", "CandidateReceipt", "LFSort",
      "LFTerm", "LFName", "LFIndex"] := by
  decide

theorem choiceUnion_signatures :
    RewriteValidationCertificate.constructorSignatures choiceUnion =
      [("=", 2), ("zero-query", 3), ("zero-query-answer", 1), ("zero-evaluate", 2),
        ("zero-evaluate-answer", 1), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-evaluate-name", 2), ("prime-need", 2), ("prime-need-answer", 2),
        ("prime-need-key", 2), ("prime-request-dependency", 1),
        ("prime-space-atom-dependency", 2), ("prime-capability-dependency", 2),
        ("prime-inert-dependency", 1), ("prime-receipt", 1), ("SortType", 0), ("SortKind", 0),
        ("Srt", 1), ("Con", 1), ("Var", 1), ("Pi", 2), ("Lam", 2), ("App", 2),
        ("c:choose", 0)] := by
  decide

theorem choiceUnion_labels :
    RewriteValidationCertificate.constructorLabels choiceUnion =
      ["=", "zero-query", "zero-query-answer", "zero-evaluate", "zero-evaluate-answer",
        "prime-unit", "prime-quote", "prime-drop", "prime-evaluate-name", "prime-need",
        "prime-need-answer", "prime-need-key", "prime-request-dependency",
        "prime-space-atom-dependency", "prime-capability-dependency", "prime-inert-dependency",
        "prime-receipt", "SortType", "SortKind", "Srt", "Con", "Var", "Pi", "Lam", "App",
        "c:choose"] := by
  decide

theorem choiceUnion_probe_checked :
    ∀ rewrite ∈ language.rewrites,
      RewriteValidationCertificate.check choiceUnion rewrite = true := by
  intro rewrite member
  change rewrite ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, evaluationDemandRewrite,
    needRewrite, needReturnRewrite, reflectedDemandRewrite] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    check_probe_rewrite choiceUnion_typeNames choiceUnion_signatures choiceUnion_labels

theorem choiceUnion_calculus_checked :
    ∀ rewrite ∈ (dkLanguage [chooseName] [chooseLeft, chooseRight]).rewrites,
      RewriteValidationCertificate.check choiceUnion rewrite = true := by
  intro rewrite member
  simp only [dkLanguage, fixedRules, List.mapIdx_cons, List.mapIdx_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    check_calculus_rewrite choiceUnion_typeNames choiceUnion_signatures choiceUnion_labels

/-- **The union with the calculus with choice passes the declaration
gate.** -/
theorem choiceUnion_validate : choiceUnion.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro equation member
    exact LanguageDef.validateEquation_eq_nil_of_plainEquationOk
      (List.all_eq_true.mp
        (by decide +kernel :
          choiceUnion.equations.all (LanguageDef.plainEquationOk choiceUnion) = true)
        equation member)
  · intro rewrite member
    refine RewriteValidationCertificate.validateRewrite_eq_nil_of_check (by decide +kernel) ?_
    rcases List.mem_append.mp member with inProbe | inCalculus
    · exact choiceUnion_probe_checked rewrite inProbe
    · exact choiceUnion_calculus_checked rewrite inCalculus

/-- The calculus with choice is presented by its two rules. -/
theorem choice_presents : Presents (withChoice Theory.empty) [chooseLeft, chooseRight] where
  undefined := fun _ => rfl
  rule_iff := fun rule => by simp [withChoice, Theory.empty]
  leftAlgebraic := by decide
  rightDetermined := by decide

/-- **Positive**: under every evaluator, the union with the calculus with
choice is a host of its scopes, on terms. -/
theorem choiceUnion_hostOf_scopes (base : BasePremiseEvaluator) :
    HostOf
      (contextTheory base
        (lambdaPiPresentation [chooseName] [chooseLeft, chooseRight] choiceUnion_validate))
      (ScopesOf (withChoice Theory.empty) [chooseName] [chooseLeft, chooseRight]) .terms
      .hosting :=
  (probeWithLambdaPi_carries _ _).hostOf_scopes choice_presents choiceUnion_validate base

/-- The union with the calculus with choice carries it. -/
theorem choiceUnion_carries : CarriesLambdaPi choiceUnion [chooseName] [chooseLeft, chooseRight] :=
  probeWithLambdaPi_carries _ _

/-- `choose Type Kind`, a closed term of the calculus with choice. -/
def chosen : (encodedRewriting (withChoice Theory.empty)
    (dkLanguage [chooseName] [chooseLeft, chooseRight]) 0).Term :=
  ⟨Dedukti.choose (.srt .type) (.srt .kind),
    encode_encodedAt (wellScoped_of_test _ 0 rfl) (by decide)⟩

/-- Its image in the union. -/
def chosenTerm : Contexts.Term choiceUnion (termInterface 0) :=
  ⟨encode chosen.1, choiceUnion_carries.encodedAt_iff.mpr chosen.2⟩

/-- **A declared rule fires under every evaluator**: in the union with the
calculus with choice, the image of `choose Type Kind` has a transition to the
image of `Type` and one to the image of `Kind`, and the two are apart. -/
theorem choiceUnion_branches (base : BasePremiseEvaluator) :
    ∃ left right : Contexts.Term choiceUnion (termInterface 0),
      TermStep base choiceUnion chosenTerm left ∧ TermStep base choiceUnion chosenTerm right ∧
        ¬ (termSetoid base choiceUnion (termInterface 0)).r left right := by
  have typeEncoded : EncodedAt (dkLanguage [chooseName] [chooseLeft, chooseRight]) 0
      (.srt .type) := encode_encodedAt (wellScoped_of_test _ 0 rfl) (by decide)
  have kindEncoded : EncodedAt (dkLanguage [chooseName] [chooseLeft, chooseRight]) 0
      (.srt .kind) := encode_encodedAt (wellScoped_of_test _ 0 rfl) (by decide)
  refine ⟨⟨encode (.srt .type), choiceUnion_carries.encodedAt_iff.mpr typeEncoded⟩,
    ⟨encode (.srt .kind), choiceUnion_carries.encodedAt_iff.mpr kindEncoded⟩, ?_, ?_, ?_⟩
  · exact (choiceUnion_carries.termStep_iff _ _).mpr
      ((choiceUnion_carries.step_encode_iff choice_presents).mpr
        ⟨_, rfl, Dedukti.step_choose_left Theory.empty _ _⟩)
  · exact (choiceUnion_carries.termStep_iff _ _).mpr
      ((choiceUnion_carries.step_encode_iff choice_presents).mpr
        ⟨_, rfl, Dedukti.step_choose_right Theory.empty _ _⟩)
  · intro related
    have same := congrArg Subtype.val ((choiceUnion_carries.termSetoid_iff _ _).mp related)
    exact absurd (encode_injective same) (by decide)

/-! ### The theory of an encoding of higher-order logic -/

/-- **The probe together with the theory of an encoding of higher-order
logic**: eight constants and the rule `term (arr a b) ⟶ term a → term b`. -/
def holUnion : LanguageDef := probeWithLambdaPi holNames [termArrow]

theorem holUnion_typeNames : holUnion.typeNames =
    ["Atom", "Space", "Process", "Alternatives", "CandidateName", "CandidateReceipt", "LFSort",
      "LFTerm", "LFName", "LFIndex"] := by
  decide

theorem holUnion_signatures :
    RewriteValidationCertificate.constructorSignatures holUnion =
      [("=", 2), ("zero-query", 3), ("zero-query-answer", 1), ("zero-evaluate", 2),
        ("zero-evaluate-answer", 1), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-evaluate-name", 2), ("prime-need", 2), ("prime-need-answer", 2),
        ("prime-need-key", 2), ("prime-request-dependency", 1),
        ("prime-space-atom-dependency", 2), ("prime-capability-dependency", 2),
        ("prime-inert-dependency", 1), ("prime-receipt", 1), ("SortType", 0), ("SortKind", 0),
        ("Srt", 1), ("Con", 1), ("Var", 1), ("Pi", 2), ("Lam", 2), ("App", 2), ("c:type", 0),
        ("c:bool", 0), ("c:arr", 0), ("c:term", 0), ("c:eq", 0), ("c:proof", 0), ("c:REFL", 0),
        ("c:ABS_THM", 0)] := by
  decide

theorem holUnion_labels :
    RewriteValidationCertificate.constructorLabels holUnion =
      ["=", "zero-query", "zero-query-answer", "zero-evaluate", "zero-evaluate-answer",
        "prime-unit", "prime-quote", "prime-drop", "prime-evaluate-name", "prime-need",
        "prime-need-answer", "prime-need-key", "prime-request-dependency",
        "prime-space-atom-dependency", "prime-capability-dependency", "prime-inert-dependency",
        "prime-receipt", "SortType", "SortKind", "Srt", "Con", "Var", "Pi", "Lam", "App",
        "c:type", "c:bool", "c:arr", "c:term", "c:eq", "c:proof", "c:REFL", "c:ABS_THM"] := by
  decide

theorem holUnion_probe_checked :
    ∀ rewrite ∈ language.rewrites,
      RewriteValidationCertificate.check holUnion rewrite = true := by
  intro rewrite member
  change rewrite ∈ [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, evaluationDemandRewrite,
    needRewrite, needReturnRewrite, reflectedDemandRewrite] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    check_probe_rewrite holUnion_typeNames holUnion_signatures holUnion_labels

theorem holUnion_calculus_checked :
    ∀ rewrite ∈ (dkLanguage holNames [termArrow]).rewrites,
      RewriteValidationCertificate.check holUnion rewrite = true := by
  intro rewrite member
  simp only [dkLanguage, fixedRules, List.mapIdx_cons, List.mapIdx_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    check_calculus_rewrite holUnion_typeNames holUnion_signatures holUnion_labels

/-- **The union with the theory of the encoding of higher-order logic passes
the declaration gate.** -/
theorem holUnion_validate : holUnion.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro equation member
    exact LanguageDef.validateEquation_eq_nil_of_plainEquationOk
      (List.all_eq_true.mp
        (by decide +kernel :
          holUnion.equations.all (LanguageDef.plainEquationOk holUnion) = true)
        equation member)
  · intro rewrite member
    refine RewriteValidationCertificate.validateRewrite_eq_nil_of_check (by decide +kernel) ?_
    rcases List.mem_append.mp member with inProbe | inCalculus
    · exact holUnion_probe_checked rewrite inProbe
    · exact holUnion_calculus_checked rewrite inCalculus

/-- **Positive**: under every evaluator, the union with the theory of the
encoding of higher-order logic is a host of its scopes, on terms. -/
theorem holUnion_hostOf_scopes (base : BasePremiseEvaluator) :
    HostOf (contextTheory base (lambdaPiPresentation holNames [termArrow] holUnion_validate))
      (ScopesOf holTheory holNames [termArrow]) .terms .hosting :=
  (probeWithLambdaPi_carries _ _).hostOf_scopes holTheory_presents holUnion_validate base

#print axioms stepAt_encode_sound_of_rewrites
#print axioms step_encode_iff_of_rewrites
#print axioms language_rewrites_match_no_encoding
#print axioms withLambdaPi_quoteDropOnly
#print axioms withLambdaPi_quoteDropSorted
#print axioms withLambdaPi_lfSorts_from
#print axioms probeWithLambdaPi_atom_not_from
#print axioms hasType_of_sortsFrom
#print axioms CarriesLambdaPi.of_quoteDrop
#print axioms dkLanguage_carries
#print axioms withLambdaPi_carries
#print axioms probeWithLambdaPi_carries
#print axioms language_not_carries
#print axioms CarriesLambdaPi.step_encode_iff
#print axioms CarriesLambdaPi.encodedAt_iff
#print axioms CarriesLambdaPi.termSetoid_iff
#print axioms CarriesLambdaPi.termStep_iff
#print axioms lambdaPiMap_hosting
#print axioms contextTheory_not_scopesOf
#print axioms CarriesLambdaPi.hostsEvery
#print axioms CarriesLambdaPi.hostOf_scopes
#print axioms lambdaPi_steps
#print axioms encodedRewriting_unboundedBranching
#print axioms matching_not_hostedBy_encodedRewriting
#print axioms matchingCandidate_not_hostOf_scopes
#print axioms grownCarried_step
#print axioms CarriesLambdaPi.not_rank
#print axioms QuoteDropOnly.not_hostOf_tabular_contexts
#print axioms pureUnion_validate
#print axioms pureUnion_hostOf_scopes
#print axioms choiceUnion_validate
#print axioms choice_presents
#print axioms choiceUnion_hostOf_scopes
#print axioms choiceUnion_branches
#print axioms holUnion_validate
#print axioms holUnion_hostOf_scopes

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
