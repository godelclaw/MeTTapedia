import Mettapedia.Logic.HostingStyles.SpacesAndRegions.SealedPart

/-!
# Sealed as written: where a name is no variable, sealing does not depend on the spelling

A term is sealed when its contraction is sealed with plain runs
(`SealedTerm`).  This module shows that, at the stages without a name and at
the types whose binders bind no name, that is the same as being sealed with
plain runs **as it is written** (`sealedTerm_iff_sealedAsWritten`): every
term of a class has the property, or none has.

The reason is one fact of the statics.  Contraction removes a quotation of a
dropping, `@*name ↦ name`.  Where every dropping drops a quotation
(`dropsQuotations`), the name that it leaves is a quotation
(`contract_dropping_of_dropsQuotations`), and a quotation is sealed beneath
any number of binders exactly when it is sealed beneath none.  So contraction
does not change whether a pattern is sealed (`sealedAt_contract_iff`), nor
whether its runs have plain spaces (`runsPlain_contract_iff`).

And every dropping drops a quotation in a term of a stage without a name
(`dropsQuotations_of_wellSorted`): a name of the candidate, where no variable
is a name, is a quotation (`eq_quoted_of_name`), because quotation is the
only constructor of names.

* **Negative, a stage with a name** (`sealedTerm_not_literal`): the quotation
  of the dropping of a name that is a variable is sealed, and is not sealed
  as it is written.
* **Negative, a type that binds a name** (`dropsVariable_not_dropsQuotations`):
  the abstraction of a name whose body drops it is a term, and it drops a
  variable.

At those stages and types the terms that are sealed as they are written are
the terms of the reflective carrier of the pattern syntax
(`reflective_iff_sealedAt`), so the sealed terms are those of that carrier
whose runs have plain spaces (`sealedTerm_iff_reflective`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef (reflectionPresentation)
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
  (contract contractList contractRoot contractList_eq_map contractRoot_quote_cases
    contract_apply_of_ne quoted dropped unitAtom QuoteDropSorted)
open Mettapedia.Logic.HostingStyles.AmbientSpace (tokens_apply_eq_zero_iff tokens_eq_zero_of_mem)
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList tokensList_eq_zero)

/-! ## Every dropping drops a quotation -/

/-- Whether a list of patterns is one quotation. -/
def isQuotationList : List Pattern → Bool
  | [.apply label [_]] => label == "prime-quote"
  | _ => false

/-- **Positive**: the quotation of the unit atom. -/
theorem isQuotationList_quoted : isQuotationList [quoted unitAtom] = true := by decide +kernel

/-- **Negative**: a variable. -/
theorem not_isQuotationList_variable : isQuotationList [.bvar 0] = false := by decide +kernel

theorem isQuotationList_iff {arguments : List Pattern} :
    isQuotationList arguments = true ↔ ∃ atom, arguments = [quoted atom] := by
  constructor
  · intro isOne
    unfold isQuotationList at isOne
    split at isOne
    · next label atom => exact ⟨atom, by rw [show label = "prime-quote" by simpa using isOne]; rfl⟩
    · cases isOne
  · rintro ⟨atom, rfl⟩
    rfl

mutual
  /-- **Every dropping in the pattern drops a quotation.** -/
  def dropsQuotations : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply label arguments =>
        (label != "prime-drop" || isQuotationList arguments) && dropsQuotationsList arguments
    | .lambda _ body => dropsQuotations body
    | .multiLambda _ _ body => dropsQuotations body
    | .subst body replacement => dropsQuotations body && dropsQuotations replacement
    | .collection _ elements _ => dropsQuotationsList elements

  /-- Every dropping in the patterns of a list drops a quotation. -/
  def dropsQuotationsList : List Pattern → Bool
    | [] => true
    | pattern :: patterns => dropsQuotations pattern && dropsQuotationsList patterns
end

/-- **Positive**: the dropped quotation of the unit atom. -/
theorem dropsQuotations_droppedQuotation : dropsQuotations (dropped (quoted unitAtom)) = true := by
  decide +kernel

/-- **Negative**: the dropping of a variable. -/
theorem not_dropsQuotations_droppedVariable : dropsQuotations (dropped (.bvar 0)) = false := by
  decide +kernel

theorem dropsQuotationsList_eq_true_iff (patterns : List Pattern) :
    dropsQuotationsList patterns = true ↔ ∀ pattern ∈ patterns, dropsQuotations pattern = true := by
  induction patterns with
  | nil => simp [dropsQuotationsList]
  | cons pattern patterns ih => simp [dropsQuotationsList, ih]

/-- The droppings of an application: what it drops, when it is a dropping,
and the droppings of its arguments. -/
theorem dropsQuotations_apply (label : String) (arguments : List Pattern) :
    dropsQuotations (.apply label arguments) = true ↔
      (label = "prime-drop" → isQuotationList arguments = true) ∧
        ∀ argument ∈ arguments, dropsQuotations argument = true := by
  rw [dropsQuotations, ← dropsQuotationsList_eq_true_iff]
  by_cases isDrop : label = "prime-drop" <;> simp [isDrop]

/-- **Where every dropping drops a quotation, the contraction of a dropping
drops a quotation, and the contraction of a quotation is a quotation.** -/
theorem contract_dropping_of_dropsQuotations (pattern : Pattern) :
    dropsQuotations pattern = true →
      (∀ name, contract pattern = dropped name → ∃ atom, name = quoted atom) ∧
        ∀ atom, pattern = quoted atom → ∃ other, contract pattern = quoted other := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro _
      exact ⟨fun name same => by (rw [contract] at same; cases same),
        fun atom same => by cases same⟩
  | hfvar name =>
      intro _
      exact ⟨fun other same => by (rw [contract] at same; cases same),
        fun atom same => by cases same⟩
  | happly label arguments ih =>
      intro drops
      obtain ⟨dropping, each⟩ := (dropsQuotations_apply label arguments).mp drops
      refine ⟨fun name same => ?_, fun atom shape => ?_⟩
      · rw [contract_apply] at same
        rcases contractRoot_cases label (arguments.map contract) with
          ⟨inner, rfl, shape, value⟩ | plain
        · rw [value] at same
          subst same
          obtain ⟨argument, rfl, contracted⟩ := List.map_eq_singleton_iff.mp shape
          obtain ⟨atom, impossible⟩ := (ih argument (by simp) (each argument (by simp))).1 _
            contracted
          simp [dropped, quoted] at impossible
        · rw [plain] at same
          simp only [dropped, Pattern.apply.injEq] at same
          obtain ⟨rfl, mapped⟩ := same
          obtain ⟨argument, rfl, contracted⟩ := List.map_eq_singleton_iff.mp mapped
          obtain ⟨atom, isOne⟩ := isQuotationList_iff.mp (dropping rfl)
          obtain rfl : argument = quoted atom := by simpa using isOne
          obtain ⟨other, quotation⟩ := (ih (quoted atom) (by simp) (each (quoted atom) (by simp))).2
            atom rfl
          exact ⟨other, contracted.symm.trans quotation⟩
      · simp only [quoted, Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        rw [contract_apply]
        simp only [List.map_cons, List.map_nil]
        rcases contractRoot_quote_cases (contract atom) with ⟨name, isDrop, value⟩ | plain
        · rw [value]
          exact (ih atom (by simp) (each atom (by simp))).1 name isDrop
        · exact ⟨contract atom, plain⟩
  | hlambda binder body _ =>
      intro _
      exact ⟨fun name same => by (rw [contract] at same; cases same),
        fun atom same => by cases same⟩
  | hmultiLambda arity binders body _ =>
      intro _
      exact ⟨fun name same => by (rw [contract] at same; cases same),
        fun atom same => by cases same⟩
  | hsubst body replacement _ _ =>
      intro _
      exact ⟨fun name same => by (rw [contract] at same; cases same),
        fun atom same => by cases same⟩
  | hcollection kind elements rest _ =>
      intro _
      exact ⟨fun name same => by (rw [contract] at same; cases same),
        fun atom same => by cases same⟩

/-! ## Contraction does not change whether a pattern is sealed -/

/-- **An application is sealed as soon as the application of changed
arguments is, when each argument is sealed as soon as its change is**,
beneath every number of binders. -/
theorem sealedAt_apply_of_map {label : String} {arguments : List Pattern}
    {change : Pattern → Pattern}
    (reflects : ∀ argument ∈ arguments, ∀ depth : Nat, sealedAt depth (change argument) = true →
      sealedAt depth argument = true)
    {depth : Nat} (safe : sealedAt depth (.apply label (arguments.map change)) = true) :
    sealedAt depth (.apply label arguments) = true := by
  by_cases isQuote : label = "prime-quote"
  · subst isQuote
    rcases arguments with _ | ⟨atom, _ | ⟨second, rest⟩⟩
    · exact safe
    · have inner : sealedAt 0 (change atom) = true := by simpa [sealedAt, binderSafeAt] using safe
      simpa [sealedAt, binderSafeAt] using reflects atom (by simp) 0 inner
    · have each := (binderSafeListAt_eq_true_iff "prime-quote" depth
        ((atom :: second :: rest).map change)).mp safe
      show binderSafeListAt "prime-quote" depth (atom :: second :: rest) = true
      rw [binderSafeListAt_eq_true_iff]
      intro argument member
      exact reflects argument member depth (each _ (List.mem_map_of_mem member))
  · rw [sealedAt_apply_of_ne isQuote] at safe ⊢
    intro argument member
    exact reflects argument member depth (safe _ (List.mem_map_of_mem member))

/-- **Where every dropping drops a quotation, a pattern is sealed exactly
when its contraction is**, beneath every number of binders. -/
theorem sealedAt_contract_iff (pattern : Pattern) :
    dropsQuotations pattern = true → ∀ depth : Nat,
      (sealedAt depth (contract pattern) = true ↔ sealedAt depth pattern = true) := by
  intro drops depth
  refine ⟨?_, sealedAt_contract pattern depth⟩
  revert depth
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth safe; rwa [contract] at safe
  | hfvar name => intro depth safe; rwa [contract] at safe
  | happly label arguments ih =>
      intro depth safe
      obtain ⟨-, each⟩ := (dropsQuotations_apply label arguments).mp drops
      rw [contract_apply] at safe
      rcases contractRoot_cases label (arguments.map contract) with
        ⟨name, rfl, shape, value⟩ | plain
      · rw [value] at safe
        obtain ⟨argument, rfl, contracted⟩ := List.map_eq_singleton_iff.mp shape
        obtain ⟨atom, rfl⟩ := (contract_dropping_of_dropsQuotations argument
          (each argument (by simp))).1 name contracted
        have beneath : sealedAt 0 (contract argument) = true := by
          rw [contracted]
          refine (sealedAt_apply_of_ne (label := "prime-drop") (by decide) 0 _).mpr
            fun inner member => ?_
          rw [List.mem_singleton.mp member, sealedAt_quoted]
          rwa [sealedAt_quoted] at safe
        have original := ih argument (by simp) (each argument (by simp)) 0 beneath
        simpa [sealedAt, binderSafeAt] using original
      · rw [plain] at safe
        exact sealedAt_apply_of_map
          (fun argument member inner => ih argument member (each argument member) inner) safe
  | hlambda binder body ih =>
      intro depth safe
      rw [dropsQuotations] at drops
      rw [contract, sealedAt_lambda] at safe
      rw [sealedAt_lambda]
      exact ih drops _ safe
  | hmultiLambda arity binders body ih =>
      intro depth safe
      rw [dropsQuotations] at drops
      rw [contract] at safe
      have inner : sealedAt (depth + arity) (contract body) = true := by
        simpa [sealedAt, binderSafeAt] using safe
      simpa [sealedAt, binderSafeAt] using ih drops _ inner
  | hsubst body replacement ihBody ihReplacement =>
      intro depth safe
      rw [dropsQuotations, Bool.and_eq_true] at drops
      rw [contract] at safe
      simp only [sealedAt, binderSafeAt, Bool.and_eq_true] at safe ⊢
      exact ⟨ihBody drops.1 _ safe.1, ihReplacement drops.2 _ safe.2⟩
  | hcollection kind elements rest ih =>
      intro depth safe
      rw [dropsQuotations, dropsQuotationsList_eq_true_iff] at drops
      rw [contract, contractList_eq_map] at safe
      simp only [sealedAt, binderSafeAt] at safe ⊢
      rw [binderSafeListAt_eq_true_iff] at safe ⊢
      intro element member
      exact ih element member (drops element member) depth (safe _ (List.mem_map_of_mem member))

/-- **Where every dropping drops a quotation, a pattern whose contraction has
no quotation and no run has none.** -/
theorem tokens_of_contract_eq_zero (pattern : Pattern) :
    dropsQuotations pattern = true → tokens quoteOrRun (contract pattern) = 0 →
      tokens quoteOrRun pattern = 0 := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ zero; rwa [contract] at zero
  | hfvar name => intro _ zero; rwa [contract] at zero
  | happly label arguments ih =>
      intro drops zero
      obtain ⟨-, each⟩ := (dropsQuotations_apply label arguments).mp drops
      rw [contract_apply] at zero
      rcases contractRoot_cases label (arguments.map contract) with
        ⟨name, rfl, shape, value⟩ | plain
      · rw [value] at zero
        obtain ⟨argument, rfl, contracted⟩ := List.map_eq_singleton_iff.mp shape
        obtain ⟨atom, rfl⟩ := (contract_dropping_of_dropsQuotations argument
          (each argument (by simp))).1 name contracted
        exact absurd (tokens_apply_eq_zero_iff.mp zero).1 (by decide)
      · rw [plain] at zero
        obtain ⟨uncounted, clean⟩ := tokens_apply_eq_zero_iff.mp zero
        exact tokens_apply_eq_zero_iff.mpr ⟨uncounted, fun argument member =>
          ih argument member (each argument member) (clean _ (List.mem_map_of_mem member))⟩
  | hlambda binder body ih =>
      intro drops zero
      rw [dropsQuotations] at drops
      rw [contract, tokens] at zero
      rw [tokens]
      exact ih drops zero
  | hmultiLambda arity binders body ih =>
      intro drops zero
      rw [dropsQuotations] at drops
      rw [contract, tokens] at zero
      rw [tokens]
      exact ih drops zero
  | hsubst body replacement ihBody ihReplacement =>
      intro drops zero
      rw [dropsQuotations, Bool.and_eq_true] at drops
      rw [contract, tokens] at zero
      rw [tokens, ihBody drops.1 (by omega), ihReplacement drops.2 (by omega)]
  | hcollection kind elements rest ih =>
      intro drops zero
      rw [dropsQuotations, dropsQuotationsList_eq_true_iff] at drops
      rw [contract, contractList_eq_map, tokens] at zero
      rw [tokens]
      exact tokensList_eq_zero fun element member =>
        ih element member (drops element member)
          (tokens_eq_zero_of_mem zero _ (List.mem_map_of_mem member))

/-- **Where every dropping drops a quotation, a space is plain exactly when
its contraction is.** -/
theorem plainSpace_contract_iff {space : Pattern} (drops : dropsQuotations space = true) :
    plainSpace (contract space) = true ↔ plainSpace space = true := by
  constructor
  · intro plain
    have quiet := tokens_of_contract_eq_zero space drops (plainSpace_iff.mp plain).2
    have fixed : contract space = space :=
      contract_of_tokens_eq_zero (counted := quoteOrRun) (by decide) space quiet
    rwa [fixed] at plain
  · intro plain
    rwa [contract_of_plainSpace plain]

/-- **Where every dropping drops a quotation, the runs of a pattern have
plain spaces exactly when those of its contraction have.** -/
theorem runsPlain_contract_iff (pattern : Pattern) :
    dropsQuotations pattern = true →
      (runsPlain (contract pattern) = true ↔ runsPlain pattern = true) := by
  intro drops
  refine ⟨?_, runsPlain_contract pattern⟩
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro plain; rwa [contract] at plain
  | hfvar name => intro plain; rwa [contract] at plain
  | happly label arguments ih =>
      intro plain
      obtain ⟨-, each⟩ := (dropsQuotations_apply label arguments).mp drops
      rw [contract_apply] at plain
      rcases contractRoot_cases label (arguments.map contract) with
        ⟨name, rfl, shape, value⟩ | same
      · rw [value] at plain
        obtain ⟨argument, rfl, contracted⟩ := List.map_eq_singleton_iff.mp shape
        have beneath : runsPlain (contract argument) = true := by
          rw [contracted]
          exact (runsPlain_apply_of_ne (label := "prime-drop") (by decide) _).mpr
            fun inner member => by
            rw [List.mem_singleton.mp member]
            exact plain
        exact (runsPlain_apply_of_ne (by decide) _).mpr fun inner member => by
          rw [List.mem_singleton.mp member]
          exact ih argument (by simp) (each argument (by simp)) beneath
      · rw [same] at plain
        obtain ⟨head, contracted⟩ := (runsPlain_apply label _).mp plain
        refine (runsPlain_apply label arguments).mpr ⟨fun isRun => ?_, fun argument member =>
          ih argument member (each argument member) (contracted _ (List.mem_map_of_mem member))⟩
        have mapped := head isRun
        cases arguments with
        | nil => rfl
        | cons space rest =>
            rw [List.map_cons, headPlain] at mapped
            rw [headPlain]
            exact (plainSpace_contract_iff (each space (by simp))).mp mapped
  | hlambda binder body ih =>
      intro plain
      rw [dropsQuotations] at drops
      rw [contract, runsPlain] at plain
      rw [runsPlain]
      exact ih drops plain
  | hmultiLambda arity binders body ih =>
      intro plain
      rw [dropsQuotations] at drops
      rw [contract, runsPlain] at plain
      rw [runsPlain]
      exact ih drops plain
  | hsubst body replacement ihBody ihReplacement =>
      intro plain
      rw [dropsQuotations, Bool.and_eq_true] at drops
      rw [contract, runsPlain, Bool.and_eq_true] at plain
      rw [runsPlain, Bool.and_eq_true]
      exact ⟨ihBody drops.1 plain.1, ihReplacement drops.2 plain.2⟩
  | hcollection kind elements rest ih =>
      intro plain
      rw [dropsQuotations, dropsQuotationsList_eq_true_iff] at drops
      rw [contract, contractList_eq_map, runsPlain, runsPlainList_eq_true_iff] at plain
      rw [runsPlain, runsPlainList_eq_true_iff]
      intro element member
      exact ih element member (drops element member) (plain _ (List.mem_map_of_mem member))

/-- **Where every dropping drops a quotation, a pattern is sealed with plain
runs exactly when its contraction is.** -/
theorem sealedWithPlainRuns_contract_iff {pattern : Pattern}
    (drops : dropsQuotations pattern = true) (depth : Nat) :
    SealedWithPlainRuns depth (contract pattern) ↔ SealedWithPlainRuns depth pattern := by
  unfold SealedWithPlainRuns
  rw [sealedAt_contract_iff pattern drops depth, runsPlain_contract_iff pattern drops]

/-! ## A name is a quotation, where no variable is a name -/

/-- Whether the domain of a binder is the sort of names. -/
def domainIsName : TypeExpr → Bool
  | .base sort => sort == "CandidateName"
  | .multiBinder (.base sort) => sort == "CandidateName"
  | _ => false

/-- **Positive**: the sort of names. -/
theorem domainIsName_name : domainIsName (.base "CandidateName") = true := by decide

/-- **Negative**: the sort of atoms. -/
theorem not_domainIsName_atom : domainIsName (.base "Atom") = false := by decide

/-- **A type whose binders bind no name.** -/
def bindsNoName : TypeExpr → Bool
  | .base _ => true
  | .arrow domain codomain => !domainIsName domain && bindsNoName codomain
  | .multiBinder body => bindsNoName body
  | .collection _ element => bindsNoName element

/-- **Positive**: the type of an abstraction of an atom. -/
theorem bindsNoName_atomAbstraction :
    bindsNoName (.arrow (.base "Atom") (.base "Atom")) = true := by decide

/-- **Negative**: the type of an abstraction of a name. -/
theorem not_bindsNoName_nameAbstraction :
    bindsNoName (.arrow (.base "CandidateName") (.base "Atom")) = false := by decide

/-- **A name is a quotation**, in a language in which quotation is the only
constructor of names, at a stage none of whose variables is a name. -/
theorem eq_quoted_of_name {lang : LanguageDef} (sorted : QuoteDropSorted lang)
    (onlyQuote : ∀ rule ∈ lang.terms, rule.category = "CandidateName" →
      rule.label = "prime-quote")
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType lang FreeTypeContext.empty bound pattern type)
    (isName : type = .base "CandidateName")
    (noNames : ∀ entry ∈ bound, entry ≠ .base "CandidateName")
    (object : isObjectPattern pattern = true) : ∃ atom, pattern = quoted atom := by
  cases typed with
  | bvar found =>
      subst isName
      exact absurd rfl (noNames _ (List.mem_of_getElem? found))
  | fvar found => simp [FreeTypeContext.empty] at found
  | @constructor _ rule arguments member bare argumentsTyped =>
      have category : rule.category = "CandidateName" := by simpa using isName
      have label := onlyQuote rule member category
      have params := (sorted.quote rule member label).2
      rw [params] at argumentsTyped
      cases argumentsTyped with
      | cons _ _ _ rest =>
          cases rest
          exact ⟨_, by rw [label]; rfl⟩
  | lambda _ => cases isName
  | multiLambda _ => cases isName
  | subst _ _ => simp [isObjectPattern] at object
  | collection _ => cases isName
  | @collectionConstructor _ rule parameterName kind elements rest elementType member shape
      elementsTyped =>
      have category : rule.category = "CandidateName" := by simpa using isName
      have params := (sorted.quote rule member (onlyQuote rule member category)).2
      rw [params] at shape
      simp at shape

/-- **What a dropping takes is a quotation**, in such a language and at such
a stage: the one argument of a dropping is a name. -/
theorem isQuotationList_of_dropArguments {lang : LanguageDef} (sorted : QuoteDropSorted lang)
    (onlyQuote : ∀ rule ∈ lang.terms, rule.category = "CandidateName" →
      rule.label = "prime-quote")
    {bound : List TypeExpr} {arguments : List Pattern}
    (typed : ArgumentsHaveTypes lang FreeTypeContext.empty bound arguments
      [.simple "name" (.base "CandidateName")])
    (noNames : ∀ entry ∈ bound, entry ≠ .base "CandidateName")
    (object : isObjectPatternList arguments = true) : isQuotationList arguments = true := by
  cases typed with
  | cons _ expected nameTyped rest =>
      cases rest
      simp only [parameterType?, Option.some.injEq] at expected
      obtain ⟨atom, rfl⟩ := eq_quoted_of_name sorted onlyQuote nameTyped expected.symm noNames
        (by simpa [isObjectPatternList] using object)
      rfl

mutual
  /-- **In a term of a stage without a name, at a type whose binders bind no
  name, every dropping drops a quotation**, in a language in which quotation
  is the only constructor of names and no constructor binds a name. -/
  theorem dropsQuotations_of_hasType {lang : LanguageDef} (sorted : QuoteDropSorted lang)
      (onlyQuote : ∀ rule ∈ lang.terms, rule.category = "CandidateName" →
        rule.label = "prime-quote")
      (params : ∀ rule ∈ lang.terms, ∀ parameter ∈ rule.params,
        ∀ expected ∈ parameterType? parameter, bindsNoName expected = true)
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType lang FreeTypeContext.empty bound pattern type)
      (noNames : ∀ entry ∈ bound, entry ≠ .base "CandidateName")
      (allowed : bindsNoName type = true) (object : isObjectPattern pattern = true) :
      dropsQuotations pattern = true := by
    cases typed with
    | bvar _ => rw [dropsQuotations]
    | fvar _ => rw [dropsQuotations]
    | @constructor _ rule arguments member _ argumentsTyped =>
        have objects : isObjectPatternList arguments = true := by
          simpa [isObjectPattern] using object
        have each := dropsQuotations_of_arguments sorted onlyQuote params argumentsTyped noNames
          (params rule member) objects
        exact (dropsQuotations_apply rule.label arguments).mpr ⟨fun isDrop =>
            isQuotationList_of_dropArguments sorted onlyQuote
              (sorted.drop rule member isDrop ▸ argumentsTyped) noNames objects,
          (dropsQuotationsList_eq_true_iff arguments).mp each⟩
    | @lambda _ binder body domain codomain bodyTyped =>
        rw [dropsQuotations]
        have parts : domainIsName domain = false ∧ bindsNoName codomain = true := by
          simpa [bindsNoName] using allowed
        refine dropsQuotations_of_hasType sorted onlyQuote params bodyTyped ?_ parts.2
          (by simpa [isObjectPattern] using object)
        intro entry member same
        rcases List.mem_cons.mp member with rfl | inBound
        · rw [same] at parts
          exact absurd parts.1 (by decide)
        · exact noNames entry inBound same
    | @multiLambda _ arity binders body domain codomain bodyTyped =>
        rw [dropsQuotations]
        have parts : domainIsName (.multiBinder domain) = false ∧ bindsNoName codomain = true := by
          simpa [bindsNoName] using allowed
        refine dropsQuotations_of_hasType sorted onlyQuote params bodyTyped ?_ parts.2
          (by simpa [isObjectPattern] using object)
        intro entry member same
        rcases List.mem_append.mp member with inBinders | inBound
        · rw [List.eq_of_mem_replicate inBinders] at same
          rw [same] at parts
          exact absurd parts.1 (by decide)
        · exact noNames entry inBound same
    | subst _ _ => simp [isObjectPattern] at object
    | collection elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        rw [dropsQuotations]
        exact dropsQuotations_of_elements sorted onlyQuote params elementsTyped noNames
          (by simpa [bindsNoName] using allowed) object.2
    | @collectionConstructor _ rule parameterName kind elements rest elementType member shape
        elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        rw [dropsQuotations]
        have element := params rule member (.simple parameterName (.collection kind elementType))
          (by rw [shape]; exact List.mem_singleton.mpr rfl) (.collection kind elementType) rfl
        exact dropsQuotations_of_elements sorted onlyQuote params elementsTyped noNames
          (by simpa [bindsNoName] using element) object.2

  /-- The same, for the arguments of a constructor. -/
  theorem dropsQuotations_of_arguments {lang : LanguageDef} (sorted : QuoteDropSorted lang)
      (onlyQuote : ∀ rule ∈ lang.terms, rule.category = "CandidateName" →
        rule.label = "prime-quote")
      (params : ∀ rule ∈ lang.terms, ∀ parameter ∈ rule.params,
        ∀ expected ∈ parameterType? parameter, bindsNoName expected = true)
      {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes lang FreeTypeContext.empty bound arguments parameters)
      (noNames : ∀ entry ∈ bound, entry ≠ .base "CandidateName")
      (allowed : ∀ parameter ∈ parameters, ∀ expected ∈ parameterType? parameter,
        bindsNoName expected = true)
      (object : isObjectPatternList arguments = true) :
      dropsQuotationsList arguments = true := by
    cases typed with
    | nil => rfl
    | cons _ expectedType argumentTyped argumentsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        rw [dropsQuotationsList,
          dropsQuotations_of_hasType sorted onlyQuote params argumentTyped noNames
            (allowed _ (List.mem_cons_self ..) _ expectedType) object.1,
          dropsQuotations_of_arguments sorted onlyQuote params argumentsTyped noNames
            (fun parameter inParams => allowed parameter (List.mem_cons_of_mem _ inParams))
            object.2]
        rfl

  /-- The same, for the elements of a collection. -/
  theorem dropsQuotations_of_elements {lang : LanguageDef} (sorted : QuoteDropSorted lang)
      (onlyQuote : ∀ rule ∈ lang.terms, rule.category = "CandidateName" →
        rule.label = "prime-quote")
      (params : ∀ rule ∈ lang.terms, ∀ parameter ∈ rule.params,
        ∀ expected ∈ parameterType? parameter, bindsNoName expected = true)
      {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType lang FreeTypeContext.empty bound elements elementType)
      (noNames : ∀ entry ∈ bound, entry ≠ .base "CandidateName")
      (allowed : bindsNoName elementType = true)
      (object : isObjectPatternList elements = true) :
      dropsQuotationsList elements = true := by
    cases typed with
    | nil => rfl
    | cons elementTyped elementsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        rw [dropsQuotationsList,
          dropsQuotations_of_hasType sorted onlyQuote params elementTyped noNames allowed object.1,
          dropsQuotations_of_elements sorted onlyQuote params elementsTyped noNames allowed
            object.2]
        rfl
end

/-! ## The candidate -/

/-- Quotation is the only constructor of names of the candidate. -/
theorem spacesAndRegions_onlyQuote : ∀ rule ∈ spacesAndRegions.terms,
    rule.category = "CandidateName" → rule.label = "prime-quote" := by
  decide

/-- No constructor of the candidate binds a name. -/
theorem spacesAndRegions_bindsNoName : ∀ rule ∈ spacesAndRegions.terms,
    ∀ parameter ∈ rule.params, ∀ expected ∈ parameterType? parameter,
      bindsNoName expected = true := by
  decide

/-- **In a term of the candidate, at a stage without a name and at a type
whose binders bind no name, every dropping drops a quotation.** -/
theorem dropsQuotations_of_wellSorted {stage : List TypeExpr} {type : TypeExpr}
    (noNames : ∀ entry ∈ stage, entry ≠ .base "CandidateName")
    (allowed : bindsNoName type = true)
    (term : Contexts.Term spacesAndRegions ⟨type, stage⟩) : dropsQuotations term.1 = true :=
  dropsQuotations_of_hasType spacesAndRegions_quoteDropSorted spacesAndRegions_onlyQuote
    spacesAndRegions_bindsNoName term.2.1 noNames allowed term.2.2.2.1

/-- The abstraction of a name whose body drops that name, as a term of the
candidate at the type of an abstraction of a name. -/
def dropsVariable :
    Contexts.Term spacesAndRegions ⟨.arrow (.base "CandidateName") (.base "Atom"), []⟩ :=
  ⟨.lambda none (dropped (.bvar 0)), checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **Negative**: at a type that binds a name a term may drop a variable. -/
theorem dropsVariable_not_dropsQuotations : dropsQuotations dropsVariable.1 = false := by
  decide +kernel

/-- **At a stage without a name and at a type whose binders bind no name, a
term is sealed exactly when it is sealed with plain runs as it is written.**
Every term of a class has the property, or none has. -/
theorem sealedTerm_iff_sealedAsWritten {stage : List TypeExpr} {type : TypeExpr}
    (noNames : ∀ entry ∈ stage, entry ≠ .base "CandidateName")
    (allowed : bindsNoName type = true)
    (term : Contexts.Term spacesAndRegions ⟨type, stage⟩) :
    SealedTerm term ↔ SealedWithPlainRuns stage.length term.1 :=
  sealedWithPlainRuns_contract_iff (dropsQuotations_of_wellSorted noNames allowed term) _

/-- **At such a stage and type the sealed terms are the terms of the
reflective carrier of the pattern syntax whose runs have plain spaces.** -/
theorem sealedTerm_iff_reflective {stage : List TypeExpr} {type : TypeExpr}
    (noNames : ∀ entry ∈ stage, entry ≠ .base "CandidateName")
    (allowed : bindsNoName type = true)
    (term : Contexts.Term spacesAndRegions ⟨type, stage⟩) :
    SealedTerm term ↔
      ReflectiveWellSorted.OpenPatternWellSorted { presentations := [reflectionPresentation] }
          spacesAndRegions FreeTypeContext.empty stage type term.1 ∧
        runsPlain term.1 = true := by
  rw [sealedTerm_iff_sealedAsWritten noNames allowed term, reflective_iff_sealedAt]
  exact ⟨fun kept => ⟨⟨term.2, kept.1⟩, kept.2⟩, fun both => ⟨both.1.2, both.2⟩⟩

#print axioms contract_dropping_of_dropsQuotations
#print axioms sealedAt_apply_of_map
#print axioms sealedAt_contract_iff
#print axioms tokens_of_contract_eq_zero
#print axioms plainSpace_contract_iff
#print axioms runsPlain_contract_iff
#print axioms sealedWithPlainRuns_contract_iff
#print axioms eq_quoted_of_name
#print axioms isQuotationList_of_dropArguments
#print axioms dropsQuotations_of_hasType
#print axioms spacesAndRegions_onlyQuote
#print axioms spacesAndRegions_bindsNoName
#print axioms dropsQuotations_of_wellSorted
#print axioms dropsVariable_not_dropsQuotations
#print axioms sealedTerm_iff_sealedAsWritten
#print axioms sealedTerm_iff_reflective

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
