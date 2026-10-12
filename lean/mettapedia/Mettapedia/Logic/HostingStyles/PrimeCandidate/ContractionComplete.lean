import Mettapedia.Logic.HostingStyles.PrimeCandidate.RunExtension
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceAdmission

/-!
# The static equivalence of the candidate is "same contraction"

`ProbeStatics` shows that the static equivalence of a language whose only
equation is that of quotation and dropping keeps the contraction of a
pattern: two terms with different contractions are apart.  This module proves
the converse, for the terms of an interface.

* A pattern reaches its contraction by removing one quotation of a dropping
  at a time (`contracts_contract`).
* When quotation and dropping have the sorts they have in the candidate
  (`QuoteDropSorted`), each removal keeps a term a term of its interface
  (`ContractStep.wellSorted`).  The typing along the context of the removal
  is the existing one (`TypedAt.replace_openPatternWellSorted`).
* So **two terms of an interface are equal exactly when they have one
  contraction** (`QuoteDropOnly.termSetoid_iff`), and the same holds of raw
  patterns (`QuoteDropOnly.equationEquiv_iff`).  Contraction is a normal form
  (`contract_contract`).

A second fact is about the sorts that quotation does not reach
(`ApartFromQuotation`): a term of such a sort contains no quotation, so it is
its own contraction (`contract_of_hasType`) and equal to no other term.  The
sort `Space` of the probe is one; its sort `Atom` is not.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.PrimeCandidate

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef (language quoteDropEquation)

/-! ## The sorts of quotation and dropping -/

/-- **Quotation and dropping have the sorts of the candidate**: quotation
takes an atom to a name, and dropping takes a name. -/
structure QuoteDropSorted (lang : LanguageDef) : Prop where
  quote : ∀ rule ∈ lang.terms, rule.label = "prime-quote" →
    rule.category = "CandidateName" ∧ rule.params = [.simple "term" (.base "Atom")]
  drop : ∀ rule ∈ lang.terms, rule.label = "prime-drop" →
    rule.params = [.simple "name" (.base "CandidateName")]

/-- **Positive**: the probe. -/
theorem language_quoteDropSorted : QuoteDropSorted language := ⟨by decide, by decide⟩

/-- **Positive**: the probe with the run constructor. -/
theorem probeWithRun_quoteDropSorted : QuoteDropSorted probeWithRun := ⟨by decide, by decide⟩

/-- A language that declares quotation at the sort of atoms. -/
def misquotedLanguage : LanguageDef :=
  { name := "misquoted"
    types := [TypeDecl.plain "Atom"]
    terms := [{ label := "prime-quote", category := "Atom",
                params := [.simple "term" (.base "Atom")], syntaxPattern := [] }]
    equations := []
    rewrites := [] }

/-- **Negative**: quotation declared at another sort. -/
theorem misquotedLanguage_not_quoteDropSorted : ¬ QuoteDropSorted misquotedLanguage := by
  intro sorted
  have category := (sorted.quote _ (List.mem_singleton.mpr rfl) rfl).1
  revert category
  decide

/-- **The quotation of a dropping has the type of what was dropped.** -/
theorem QuoteDropSorted.typed {lang : LanguageDef} (sorted : QuoteDropSorted lang)
    {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern} {type : TypeExpr}
    (typed : HasType lang free bound (quoted (dropped name)) type) :
    HasType lang free bound name type := by
  obtain ⟨rule, member, label, -, rfl, arguments⟩ := hasType_apply_inversion typed
  obtain ⟨category, parameters⟩ := sorted.quote rule member label.symm
  rw [parameters] at arguments
  obtain ⟨inner, -⟩ := arguments.simple_cons_inv
  obtain ⟨dropRule, dropMember, dropLabel, -, -, dropArguments⟩ := hasType_apply_inversion inner
  rw [sorted.drop dropRule dropMember dropLabel.symm] at dropArguments
  rw [category]
  exact dropArguments.simple_cons_inv.1

/-! ## Removing one quotation of a dropping -/

/-- **One removal**: a quotation of a dropping, at one place of a pattern, is
replaced by what was dropped. -/
inductive ContractStep : Pattern → Pattern → Prop where
  | inContext (context : OneHoleContext) (name : Pattern) :
      ContractStep (context.fill (quoted (dropped name))) (context.fill name)

/-- Finitely many removals. -/
abbrev Contracts : Pattern → Pattern → Prop := Relation.ReflTransGen ContractStep

theorem ContractStep.fill (context : OneHoleContext) {source target : Pattern}
    (step : ContractStep source target) :
    ContractStep (context.fill source) (context.fill target) := by
  cases step with
  | inContext inner name =>
      rw [← OneHoleContext.fill_comp, ← OneHoleContext.fill_comp]
      exact .inContext (context.comp inner) name

theorem Contracts.fill (context : OneHoleContext) {source target : Pattern}
    (steps : Contracts source target) : Contracts (context.fill source) (context.fill target) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.fill context)

/-- The arguments of an application are contracted one after the other. -/
theorem contracts_apply (label : String) :
    ∀ (before after : List Pattern),
      (∀ argument ∈ after, Contracts argument (contract argument)) →
        Contracts (.apply label (before ++ after)) (.apply label (before ++ after.map contract))
  | before, [], _ => by simpa using Relation.ReflTransGen.refl
  | before, argument :: rest, each => by
      have head : Contracts (.apply label (before ++ argument :: rest))
          (.apply label (before ++ contract argument :: rest)) :=
        (each argument (List.mem_cons_self ..)).fill (.apply label before .hole rest)
      have tail := contracts_apply label (before ++ [contract argument]) rest
        fun other member => each other (List.mem_cons_of_mem _ member)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at tail
      exact head.trans tail

/-- So are the members of a collection. -/
theorem contracts_collection (kind : CollType) (tail : Option String) :
    ∀ (before after : List Pattern),
      (∀ element ∈ after, Contracts element (contract element)) →
        Contracts (.collection kind (before ++ after) tail)
          (.collection kind (before ++ after.map contract) tail)
  | before, [], _ => by simpa using Relation.ReflTransGen.refl
  | before, element :: rest, each => by
      have head : Contracts (.collection kind (before ++ element :: rest) tail)
          (.collection kind (before ++ contract element :: rest) tail) :=
        (each element (List.mem_cons_self ..)).fill (.collection kind before .hole rest tail)
      have others := contracts_collection kind tail (before ++ [contract element]) rest
        fun other member => each other (List.mem_cons_of_mem _ member)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at others
      exact head.trans others

/-- The contraction at the root is at most one removal. -/
theorem contracts_contractRoot (label : String) (arguments : List Pattern) :
    Contracts (.apply label arguments) (contractRoot label arguments) := by
  unfold contractRoot
  split_ifs with isQuote
  · subst isQuote
    split
    · next inner name =>
        split_ifs with isDrop
        · subst isDrop
          exact .single (.inContext .hole name)
        · exact .refl
    · exact .refl
  · exact .refl

/-- **A pattern reaches its contraction by removals.** -/
theorem contracts_contract (pattern : Pattern) : Contracts pattern (contract pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rw [contract]
  | hfvar name => rw [contract]
  | happly label arguments ih =>
      have inner := contracts_apply label [] arguments ih
      rw [contract, contractList_eq_map]
      exact (by simpa using inner : Contracts (.apply label arguments)
        (.apply label (arguments.map contract))).trans (contracts_contractRoot label _)
  | hlambda binder body ih =>
      rw [contract]
      exact ih.fill (.lambda binder .hole)
  | hmultiLambda arity binders body ih =>
      rw [contract]
      exact ih.fill (.multiLambda arity binders .hole)
  | hsubst body replacement ihBody ihReplacement =>
      rw [contract]
      exact (ihBody.fill (.substBody .hole replacement)).trans
        (ihReplacement.fill (.substReplacement (contract body) .hole))
  | hcollection kind elements rest ih =>
      have inner := contracts_collection kind rest [] elements ih
      rw [contract, contractList_eq_map]
      simpa using inner

/-- A removal is one generator of the static equivalence. -/
theorem ContractStep.equationContextStep (base : BasePremiseEvaluator) {lang : LanguageDef}
    (authored : quoteDropEquation ∈ lang.equations) {source target : Pattern}
    (step : ContractStep source target) : EquationContextStep base lang source target := by
  cases step with
  | inContext context name => exact quoteDrop_contextStep base authored context name

/-- **A pattern and its contraction are equal**, in a language with the
equation of quotation and dropping. -/
theorem equationEquiv_contract (base : BasePremiseEvaluator) {lang : LanguageDef}
    (authored : quoteDropEquation ∈ lang.equations) (pattern : Pattern) :
    EquationEquiv base lang pattern (contract pattern) := by
  have chain : ∀ {source target : Pattern}, Contracts source target →
      EquationEquiv base lang source target := by
    intro source target steps
    induction steps with
    | refl => exact .refl _
    | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ (step.equationContextStep base authored))
  exact chain (contracts_contract pattern)

theorem QuoteDropOnly.authored {lang : LanguageDef} (only : QuoteDropOnly lang) :
    quoteDropEquation ∈ lang.equations :=
  only.equations ▸ List.mem_singleton.mpr rfl

/-- **Two patterns are equal exactly when they have one contraction.** -/
theorem QuoteDropOnly.equationEquiv_iff {lang : LanguageDef} (only : QuoteDropOnly lang)
    {base : BasePremiseEvaluator} {left right : Pattern} :
    EquationEquiv base lang left right ↔ contract left = contract right := by
  constructor
  · exact fun equivalent => (only.equiv equivalent).1
  · intro same
    refine .trans _ _ _ (equationEquiv_contract base only.authored left) ?_
    rw [same]
    exact .symm _ _ (equationEquiv_contract base only.authored right)

/-! ## A removal keeps a term a term -/

/-- An application may be replaced by any pattern without a change of the
representation that the parameters around it ask for. -/
theorem representationCompatible_of_apply (label : String) (arguments : List Pattern)
    (target : Pattern) : RepresentationCompatible (.apply label arguments) target := by
  intro context parameter represented
  cases context with
  | hole => cases parameter <;> simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | apply _ _ _ _ =>
      cases parameter <;> simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | lambda binder _ =>
      cases binder <;> cases parameter <;>
        simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | multiLambda _ binders _ =>
      cases binders <;> cases parameter <;>
        simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | substBody _ _ =>
      cases parameter <;> simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | substReplacement _ _ =>
      cases parameter <;> simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | collection _ _ _ _ _ =>
      cases parameter <;> simp_all [MatchesParameterRepresentation, OneHoleContext.fill]

/-- A quotation of a dropping and what was dropped pass the same checks of
binder names, of object form and of scope. -/
theorem admissionProfile_quoted_dropped (name : Pattern) :
    AdmissionProfileEquivalent (quoted (dropped name)) name :=
  ⟨by simp [quoted, dropped, Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList],
    by simp [quoted, dropped, isObjectPattern, isObjectPatternList],
    fun depth => by simp [quoted, dropped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]⟩

/-- **A removal keeps a term a term of its interface.** -/
theorem ContractStep.wellSorted {lang : LanguageDef} (sorted : QuoteDropSorted lang)
    {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
    (step : ContractStep source target)
    (admitted : OpenPatternWellSorted lang free bound type source) :
    OpenPatternWellSorted lang free bound type target := by
  cases step with
  | inContext context name =>
      obtain ⟨focusBound, result, selected⟩ := hasType_typedAt context admitted.1
      exact selected.replace_openPatternWellSorted admitted
        (representationCompatible_of_apply _ _ name) (admissionProfile_quoted_dropped name)
        (sorted.typed selected.focus_typed)

/-- Removals relate a term to a term of the same interface, and the two are
equal there. -/
theorem Contracts.termSetoid {lang : LanguageDef} (only : QuoteDropOnly lang)
    (sorted : QuoteDropSorted lang) (base : BasePremiseEvaluator)
    {interface : Contexts.Interface} {source target : Pattern} (steps : Contracts source target) :
    ∀ admitted : OpenPatternWellSorted lang FreeTypeContext.empty interface.stage interface.type
        source,
      ∃ reached : OpenPatternWellSorted lang FreeTypeContext.empty interface.stage interface.type
          target,
        (termSetoid base lang interface).r ⟨source, admitted⟩ ⟨target, reached⟩ := by
  induction steps with
  | refl => exact fun admitted => ⟨admitted, Relation.EqvGen.refl _⟩
  | tail _ step ih =>
      intro admitted
      obtain ⟨middle, related⟩ := ih admitted
      refine ⟨step.wellSorted sorted middle, ?_⟩
      exact Relation.EqvGen.trans _ _ _ related
        (Relation.EqvGen.rel _ _ (step.equationContextStep base only.authored))

/-- **The contraction of a term is a term of its interface.** -/
theorem contract_wellSorted {lang : LanguageDef} (sorted : QuoteDropSorted lang)
    {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr} {pattern : Pattern}
    (admitted : OpenPatternWellSorted lang free bound type pattern) :
    OpenPatternWellSorted lang free bound type (contract pattern) := by
  have chain : ∀ {target : Pattern}, Contracts pattern target →
      OpenPatternWellSorted lang free bound type target := by
    intro target steps
    induction steps with
    | refl => exact admitted
    | tail _ step ih => exact step.wellSorted sorted ih
  exact chain (contracts_contract pattern)

/-- The contraction of a term, as a term. -/
def contractTerm {lang : LanguageDef} (sorted : QuoteDropSorted lang)
    {interface : Contexts.Interface} (term : Contexts.Term lang interface) :
    Contexts.Term lang interface :=
  ⟨contract term.1, contract_wellSorted sorted term.2⟩

/-- **A term is equal to its contraction.** -/
theorem termSetoid_contractTerm {lang : LanguageDef} (only : QuoteDropOnly lang)
    (sorted : QuoteDropSorted lang) (base : BasePremiseEvaluator)
    {interface : Contexts.Interface} (term : Contexts.Term lang interface) :
    (termSetoid base lang interface).r term (contractTerm sorted term) := by
  obtain ⟨reached, related⟩ :=
    (contracts_contract term.1).termSetoid only sorted base (interface := interface) term.2
  exact related

/-- **Two terms of an interface are equal exactly when they have one
contraction.**  Contraction decides the static equivalence of the
candidate. -/
theorem QuoteDropOnly.termSetoid_iff {lang : LanguageDef} (only : QuoteDropOnly lang)
    (sorted : QuoteDropSorted lang) {base : BasePremiseEvaluator}
    {interface : Contexts.Interface} {first second : Contexts.Term lang interface} :
    (termSetoid base lang interface).r first second ↔ contract first.1 = contract second.1 := by
  constructor
  · exact fun related => only.contract_eq related
  · intro same
    have middle : contractTerm sorted first = contractTerm sorted second := Subtype.ext same
    exact (termSetoid base lang interface).iseqv.trans
      (termSetoid_contractTerm only sorted base first)
      (middle ▸ (termSetoid base lang interface).iseqv.symm
        (termSetoid_contractTerm only sorted base second))

/-- The contraction at the root of contracted arguments has nothing to
contract. -/
theorem contract_contractRoot {label : String} {arguments : List Pattern}
    (fixed : arguments.map contract = arguments) :
    contract (contractRoot label arguments) = contractRoot label arguments := by
  have whole : contract (.apply label arguments) = contractRoot label arguments := by
    rw [contract, contractList_eq_map, fixed]
  by_cases shape : ∃ name, label = "prime-quote" ∧ arguments = [.apply "prime-drop" [name]]
  · obtain ⟨name, rfl, rfl⟩ := shape
    have inner : contract (.apply "prime-drop" [name]) = .apply "prime-drop" [name] := by
      simpa using fixed
    rw [contract_apply_of_ne (by decide)] at inner
    have nameFixed : contract name = name := by simpa using inner
    simpa [contractRoot] using nameFixed
  · have plain : contractRoot label arguments = .apply label arguments := by
      by_cases isQuote : label = "prime-quote"
      · subst isQuote
        rcases arguments with _ | ⟨head, _ | ⟨second, rest⟩⟩
        · simp [contractRoot]
        · cases head with
          | apply inner innerArguments =>
              rcases innerArguments with _ | ⟨name, _ | ⟨other, more⟩⟩
              · simp [contractRoot]
              · by_cases isDrop : inner = "prime-drop"
                · exact absurd ⟨name, rfl, by rw [isDrop]⟩ shape
                · simp [contractRoot, isDrop]
              · simp [contractRoot]
          | _ => simp [contractRoot]
        · simp [contractRoot]
      · simp [contractRoot, isQuote]
    rw [plain]
    exact whole.trans plain

/-- **Contraction is a normal form**: a contraction has nothing to
contract. -/
theorem contract_contract (pattern : Pattern) : contract (contract pattern) = contract pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rw [contract, contract]
  | hfvar name => rw [contract, contract]
  | happly label arguments ih =>
      have inner : (arguments.map contract).map contract = arguments.map contract := by
        rw [List.map_map]
        exact List.map_congr_left fun argument member => ih argument member
      rw [contract, contractList_eq_map]
      exact contract_contractRoot inner
  | hlambda binder body ih => rw [contract, contract, ih]
  | hmultiLambda arity binders body ih => rw [contract, contract, ih]
  | hsubst body replacement ihBody ihReplacement =>
      rw [contract, contract, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      rw [contract, contract, contractList_eq_map, contractList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => ih element member

/-! ## Sorts that quotation does not reach -/

/-- The sorts at which a type expression ends lie in a list. -/
def resultIn (sorts : List String) : TypeExpr → Bool
  | .base sort => sorts.contains sort
  | .arrow _ codomain => resultIn sorts codomain
  | .multiBinder body => resultIn sorts body
  | .collection _ element => resultIn sorts element

/-- **Sorts apart from quotation**: no constructor of these sorts is
quotation, and every constructor of these sorts takes arguments of these
sorts. -/
def ApartFromQuotation (lang : LanguageDef) (sorts : List String) : Prop :=
  ∀ rule ∈ lang.terms, rule.category ∈ sorts →
    rule.label ≠ "prime-quote" ∧
      ∀ parameter ∈ rule.params, ∀ expected ∈ parameterType? parameter,
        resultIn sorts expected = true

/-- **Positive**: the sort `Space` of the probe with the run constructor,
which has no constructor at all. -/
theorem probeWithRun_space_apart : ApartFromQuotation probeWithRun ["Space"] := by
  intro rule member category
  simp only [List.mem_singleton] at category
  exact (probeWithRun_category_ne_space rule member category).elim

/-- **Negative**: the sort of atoms, where a dropping takes a name. -/
theorem probeWithRun_atom_not_apart : ¬ ApartFromQuotation probeWithRun ["Atom"] := by
  intro apart
  have dropped := (apart Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.dropConstructor
    (by decide) (by decide)).2 (.simple "name" (.base "CandidateName")) (by decide)
    (.base "CandidateName") rfl
  revert dropped
  decide

mutual
  /-- **A term of a sort apart from quotation is its own contraction.** -/
  theorem contract_of_hasType {lang : LanguageDef} {sorts : List String}
      (apart : ApartFromQuotation lang sorts) {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr} (typed : HasType lang free bound pattern type)
      (inSorts : resultIn sorts type = true) (object : isObjectPattern pattern = true) :
      contract pattern = pattern := by
    cases typed with
    | bvar _ => rw [contract]
    | fvar _ => rw [contract]
    | @constructor _ rule arguments member _ argumentsTyped =>
        have category : rule.category ∈ sorts := by simpa [resultIn] using inSorts
        obtain ⟨other, parameters⟩ := apart rule member category
        rw [contract_apply_of_ne other,
          contractList_of_arguments apart argumentsTyped parameters
            (by simpa [isObjectPattern] using object)]
    | lambda bodyTyped =>
        rw [contract, contract_of_hasType apart bodyTyped (by simpa [resultIn] using inSorts)
          (by simpa [isObjectPattern] using object)]
    | multiLambda bodyTyped =>
        rw [contract, contract_of_hasType apart bodyTyped (by simpa [resultIn] using inSorts)
          (by simpa [isObjectPattern] using object)]
    | subst _ _ => simp [isObjectPattern] at object
    | collection elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        rw [contract, contractList_eq_map,
          contractList_of_elements apart elementsTyped (by simpa [resultIn] using inSorts)
            object.2]
    | @collectionConstructor _ rule parameterName kind elements rest elementType member shape
        elementsTyped =>
        have category : rule.category ∈ sorts := by simpa [resultIn] using inSorts
        have element := (apart rule member category).2 (.simple parameterName
          (.collection kind elementType)) (by rw [shape]; exact List.mem_singleton.mpr rfl)
          (.collection kind elementType) rfl
        simp only [isObjectPattern, Bool.and_eq_true] at object
        rw [contract, contractList_eq_map,
          contractList_of_elements apart elementsTyped (by simpa [resultIn] using element)
            object.2]

  theorem contractList_of_arguments {lang : LanguageDef} {sorts : List String}
      (apart : ApartFromQuotation lang sorts) {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes lang free bound arguments parameters)
      (inSorts : ∀ parameter ∈ parameters, ∀ expected ∈ parameterType? parameter,
        resultIn sorts expected = true)
      (object : isObjectPatternList arguments = true) : arguments.map contract = arguments := by
    cases typed with
    | nil => rfl
    | cons _ expectedType argumentTyped argumentsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        rw [List.map_cons,
          contract_of_hasType apart argumentTyped
            (inSorts _ (List.mem_cons_self ..) _ expectedType) object.1,
          contractList_of_arguments apart argumentsTyped
            (fun parameter member => inSorts parameter (List.mem_cons_of_mem _ member)) object.2]

  theorem contractList_of_elements {lang : LanguageDef} {sorts : List String}
      (apart : ApartFromQuotation lang sorts) {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType lang free bound elements elementType)
      (inSorts : resultIn sorts elementType = true)
      (object : isObjectPatternList elements = true) : elements.map contract = elements := by
    cases typed with
    | nil => rfl
    | cons elementTyped elementsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        rw [List.map_cons, contract_of_hasType apart elementTyped inSorts object.1,
          contractList_of_elements apart elementsTyped inSorts object.2]
end

#print axioms QuoteDropSorted.typed
#print axioms contracts_contract
#print axioms QuoteDropOnly.equationEquiv_iff
#print axioms ContractStep.wellSorted
#print axioms contract_wellSorted
#print axioms QuoteDropOnly.termSetoid_iff
#print axioms contract_contract
#print axioms contract_of_hasType
#print axioms probeWithRun_atom_not_apart
#print axioms misquotedLanguage_not_quoteDropSorted

end Mettapedia.Logic.HostingStyles.PrimeCandidate
