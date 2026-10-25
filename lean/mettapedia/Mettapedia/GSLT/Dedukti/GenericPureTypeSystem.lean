import Mettapedia.GSLT.Dedukti.TypeInTypeParadox

/-!
# Pure type systems over an arbitrary collection of sorts

The maintained `PureTypeSystem` presentation uses the two concrete LF sorts.
This module supplies the sort-parametric layer needed to compare calculi whose
universe strata differ.  A morphism maps sorts and preserves sort axioms and
product rules; its action on annotated terms transports beta conversion and
typing derivations.

The final section connects this layer to the existing two-sort presentation.
It is therefore a generalization of that formation and typing discipline, not
an unrelated calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.GenericPureTypeSystem

universe u v w

/-- A product-formation rule over an arbitrary sort carrier. -/
structure ProductRule (SortCode : Type u) where
  domain : SortCode
  codomain : SortCode
  result : SortCode
  deriving DecidableEq, Repr

namespace ProductRule

/-- Rename every sort in a product rule. -/
def map {Source : Type u} {Target : Type v} (rename : Source → Target)
    (rule : ProductRule Source) : ProductRule Target :=
  ⟨rename rule.domain, rename rule.codomain, rename rule.result⟩

@[simp] theorem map_domain {Source : Type u} {Target : Type v}
    (rename : Source → Target) (rule : ProductRule Source) :
    (rule.map rename).domain = rename rule.domain := rfl

@[simp] theorem map_codomain {Source : Type u} {Target : Type v}
    (rename : Source → Target) (rule : ProductRule Source) :
    (rule.map rename).codomain = rename rule.codomain := rfl

@[simp] theorem map_result {Source : Type u} {Target : Type v}
    (rename : Source → Target) (rule : ProductRule Source) :
    (rule.map rename).result = rename rule.result := rfl

@[simp] theorem map_id {SortCode : Type u} (rule : ProductRule SortCode) :
    rule.map id = rule := by cases rule; rfl

theorem map_comp {First : Type u} {Second : Type v} {Third : Type w}
    (second : Second → Third) (first : First → Second)
    (rule : ProductRule First) :
    (rule.map first).map second = rule.map (second ∘ first) := by
  cases rule
  rfl

end ProductRule

/-- A relational presentation permits any sort carrier while keeping
functionality as an explicit property. -/
structure Profile (SortCode : Type u) where
  Axiom : SortCode → SortCode → Prop
  Product : ProductRule SortCode → Prop

/-- Both sort axioms and product results are single-valued. -/
def Functional {SortCode : Type u} (profile : Profile SortCode) : Prop :=
  (∀ {source first second}, profile.Axiom source first →
      profile.Axiom source second → first = second) ∧
    ∀ {first second}, profile.Product first → profile.Product second →
      first.domain = second.domain → first.codomain = second.codomain →
        first.result = second.result

/-- A sort-renaming morphism of pure-type-system profiles. -/
structure Morphism {Source : Type u} {Target : Type v}
    (source : Profile Source) (target : Profile Target) where
  onSort : Source → Target
  axiom_preserved : ∀ {first second}, source.Axiom first second →
    target.Axiom (onSort first) (onSort second)
  product_preserved : ∀ {rule}, source.Product rule →
    target.Product (rule.map onSort)

namespace Morphism

def id {SortCode : Type u} (profile : Profile SortCode) : Morphism profile profile where
  onSort := fun sort => sort
  axiom_preserved := fun known => known
  product_preserved := by
    intro rule known
    simpa [ProductRule.map] using known

def comp {First : Type u} {Second : Type v} {Third : Type w}
    {first : Profile First} {second : Profile Second} {third : Profile Third}
    (later : Morphism second third) (earlier : Morphism first second) :
    Morphism first third where
  onSort := later.onSort ∘ earlier.onSort
  axiom_preserved := fun known => later.axiom_preserved (earlier.axiom_preserved known)
  product_preserved := by
    intro rule known
    simpa [ProductRule.map_comp] using
      later.product_preserved (earlier.product_preserved known)

end Morphism

/-- Sort-annotated terms of a generic pure type system. -/
inductive Term (SortCode : Type u) where
  | var : Nat → Term SortCode
  | sort : SortCode → Term SortCode
  | pi : ProductRule SortCode → Term SortCode → Term SortCode → Term SortCode
  | lam : SortCode → Term SortCode → Term SortCode → Term SortCode
  | app : Term SortCode → Term SortCode → Term SortCode
  deriving DecidableEq, Repr

namespace Term

def lift {SortCode : Type u} (amount cutoff : Nat) : Term SortCode → Term SortCode
  | .var index => .var (if index < cutoff then index else index + amount)
  | .sort level => .sort level
  | .pi rule domain body =>
      .pi rule (lift amount cutoff domain) (lift amount (cutoff + 1) body)
  | .lam level domain body =>
      .lam level (lift amount cutoff domain) (lift amount (cutoff + 1) body)
  | .app function argument => .app (lift amount cutoff function) (lift amount cutoff argument)

def subst {SortCode : Type u} (target : Nat) (replacement : Term SortCode) :
    Term SortCode → Term SortCode
  | .var index =>
      if index = target then replacement
      else if target < index then .var (index - 1)
      else .var index
  | .sort level => .sort level
  | .pi rule domain body =>
      .pi rule (subst target replacement domain)
        (subst (target + 1) (lift 1 0 replacement) body)
  | .lam level domain body =>
      .lam level (subst target replacement domain)
        (subst (target + 1) (lift 1 0 replacement) body)
  | .app function argument =>
      .app (subst target replacement function) (subst target replacement argument)

def subst0 {SortCode : Type u} (argument body : Term SortCode) : Term SortCode :=
  subst 0 argument body

/-- Rename the sorts in an annotated term. -/
def map {Source : Type u} {Target : Type v} (rename : Source → Target) :
    Term Source → Term Target
  | .var index => .var index
  | .sort level => .sort (rename level)
  | .pi rule domain body => .pi (rule.map rename) (map rename domain) (map rename body)
  | .lam level domain body => .lam (rename level) (map rename domain) (map rename body)
  | .app function argument => .app (map rename function) (map rename argument)

@[simp] theorem map_lift {Source : Type u} {Target : Type v}
    (rename : Source → Target) (term : Term Source) :
    ∀ amount cutoff, map rename (lift amount cutoff term) =
      lift amount cutoff (map rename term) := by
  induction term with
  | var index => intro amount cutoff; simp [lift, map]
  | sort level => intro amount cutoff; rfl
  | pi rule domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, map, ihDomain, ihBody]
  | lam level domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, map, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro amount cutoff; simp [lift, map, ihFunction, ihArgument]

@[simp] theorem map_subst {Source : Type u} {Target : Type v}
    (rename : Source → Target) (term : Term Source) :
    ∀ target replacement,
      map rename (subst target replacement term) =
        subst target (map rename replacement) (map rename term) := by
  induction term with
  | var index =>
      intro target replacement
      by_cases same : index = target
      · simp [subst, map, same]
      · by_cases earlier : target < index <;> simp [subst, map, same, earlier]
  | sort level => intro target replacement; rfl
  | pi rule domain body ihDomain ihBody =>
      intro target replacement
      simp [subst, map, ihDomain, ihBody]
  | lam level domain body ihDomain ihBody =>
      intro target replacement
      simp [subst, map, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro target replacement
      simp [subst, map, ihFunction, ihArgument]

@[simp] theorem map_subst0 {Source : Type u} {Target : Type v}
    (rename : Source → Target) (argument body : Term Source) :
    map rename (subst0 argument body) =
      subst0 (map rename argument) (map rename body) :=
  map_subst rename body 0 argument

@[simp] theorem map_id {SortCode : Type u} (term : Term SortCode) :
    map id term = term := by
  induction term <;> simp_all [map]

theorem map_comp {First : Type u} {Second : Type v} {Third : Type w}
    (second : Second → Third) (first : First → Second) (term : Term First) :
    map second (map first term) = map (second ∘ first) term := by
  induction term <;> simp_all [map, ProductRule.map_comp]

end Term

/-- Contextual beta reduction. -/
inductive Step {SortCode : Type u} : Term SortCode → Term SortCode → Prop where
  | beta (level : SortCode) (domain body argument : Term SortCode) :
      Step (.app (.lam level domain body) argument) (Term.subst0 argument body)
  | piDomain {rule : ProductRule SortCode} {domain domain' body : Term SortCode} :
      Step domain domain' → Step (.pi rule domain body) (.pi rule domain' body)
  | piBody {rule : ProductRule SortCode} {domain body body' : Term SortCode} :
      Step body body' → Step (.pi rule domain body) (.pi rule domain body')
  | lamDomain {level : SortCode} {domain domain' body : Term SortCode} :
      Step domain domain' → Step (.lam level domain body) (.lam level domain' body)
  | lamBody {level : SortCode} {domain body body' : Term SortCode} :
      Step body body' → Step (.lam level domain body) (.lam level domain body')
  | appFunction {function function' argument : Term SortCode} :
      Step function function' → Step (.app function argument) (.app function' argument)
  | appArgument {function argument argument' : Term SortCode} :
      Step argument argument' → Step (.app function argument) (.app function argument')

abbrev Conv {SortCode : Type u} : Term SortCode → Term SortCode → Prop :=
  Relation.EqvGen Step

theorem Step.map {Source : Type u} {Target : Type v} (rename : Source → Target)
    {source target : Term Source} (step : Step source target) :
    Step (Term.map rename source) (Term.map rename target) := by
  induction step with
  | beta level domain body argument =>
      simpa [Term.map] using
        (Step.beta (rename level) (Term.map rename domain) (Term.map rename body)
          (Term.map rename argument))
  | piDomain step ih => exact .piDomain ih
  | piBody step ih => exact .piBody ih
  | lamDomain step ih => exact .lamDomain ih
  | lamBody step ih => exact .lamBody ih
  | appFunction step ih => exact .appFunction ih
  | appArgument step ih => exact .appArgument ih

theorem Conv.map {Source : Type u} {Target : Type v} (rename : Source → Target)
    {source target : Term Source} (convertible : Conv source target) :
    Conv (Term.map rename source) (Term.map rename target) := by
  induction convertible with
  | rel _ _ step => exact .rel _ _ (step.map rename)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-- The two forms of a sort-annotated PTS judgment. -/
inductive Judgment (SortCode : Type u) where
  | type (subject : Term SortCode) (sort : SortCode)
  | term (subject type : Term SortCode) (sort : SortCode)
  deriving DecidableEq, Repr

namespace Judgment

def map {Source : Type u} {Target : Type v} (rename : Source → Target) :
    Judgment Source → Judgment Target
  | .type subject sort => .type (Term.map rename subject) (rename sort)
  | .term subject typeExpr sort =>
      .term (Term.map rename subject) (Term.map rename typeExpr) (rename sort)

end Judgment

abbrev SortedCtx (SortCode : Type u) := List (Term SortCode × SortCode)

def mapContext {Source : Type u} {Target : Type v} (rename : Source → Target)
    (context : SortedCtx Source) : SortedCtx Target :=
  match context with
  | [] => []
  | (term, sort) :: rest =>
      (Term.map rename term, rename sort) :: mapContext rename rest

theorem mapContext_eq_map {Source : Type u} {Target : Type v}
    (rename : Source → Target) (context : SortedCtx Source) :
    mapContext rename context =
      context.map fun entry => (Term.map rename entry.1, rename entry.2) := by
  induction context with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨term, sort⟩
      simp [mapContext, ih]

def lookupSorted {SortCode : Type u} (context : SortedCtx SortCode) (index : Nat) :
    Option (Term SortCode × SortCode) :=
  (context[index]?).map fun entry => (Term.lift (index + 1) 0 entry.1, entry.2)

theorem lookupSorted_map {Source : Type u} {Target : Type v}
    (rename : Source → Target) (context : SortedCtx Source) (index : Nat) :
    lookupSorted (mapContext rename context) index =
      (lookupSorted context index).map fun entry =>
        (Term.map rename entry.1, rename entry.2) := by
  rw [mapContext_eq_map]
  simp only [lookupSorted, List.getElem?_map, Option.map_map]
  cases context[index]? with
  | none => rfl
  | some entry =>
      rcases entry with ⟨term, sort⟩
      simp

/-- Generic sort-annotated PTS typing. -/
inductive Derives {SortCode : Type u} (profile : Profile SortCode) :
    SortedCtx SortCode → Judgment SortCode → Prop where
  | sort {context : SortedCtx SortCode} {source target : SortCode} :
      profile.Axiom source target →
      Derives profile context (.type (.sort source) target)
  | pi {context : SortedCtx SortCode} {domain body : Term SortCode}
      {domainSort codomainSort resultSort : SortCode} :
      Derives profile context (.type domain domainSort) →
      Derives profile ((domain, domainSort) :: context) (.type body codomainSort) →
      profile.Product ⟨domainSort, codomainSort, resultSort⟩ →
      Derives profile context
        (.type (.pi ⟨domainSort, codomainSort, resultSort⟩ domain body) resultSort)
  | ofTerm {context : SortedCtx SortCode} {subject : Term SortCode}
      {sort above : SortCode} :
      Derives profile context (.term subject (.sort sort) above) →
      profile.Axiom sort above →
      Derives profile context (.type subject sort)
  | toTerm {context : SortedCtx SortCode} {subject : Term SortCode}
      {sort above : SortCode} :
      Derives profile context (.type subject sort) →
      profile.Axiom sort above →
      Derives profile context (.term subject (.sort sort) above)
  | var {context : SortedCtx SortCode} {index : Nat} {type : Term SortCode}
      {sort : SortCode} :
      lookupSorted context index = some (type, sort) →
      Derives profile context (.term (.var index) type sort)
  | lam {context : SortedCtx SortCode} {domain body bodyType : Term SortCode}
      {domainSort codomainSort resultSort : SortCode} :
      Derives profile context (.type domain domainSort) →
      Derives profile ((domain, domainSort) :: context) (.type bodyType codomainSort) →
      profile.Product ⟨domainSort, codomainSort, resultSort⟩ →
      Derives profile ((domain, domainSort) :: context) (.term body bodyType codomainSort) →
      Derives profile context
        (.term (.lam domainSort domain body)
          (.pi ⟨domainSort, codomainSort, resultSort⟩ domain bodyType) resultSort)
  | app {context : SortedCtx SortCode}
      {function argument domain body : Term SortCode}
      {domainSort codomainSort resultSort : SortCode} :
      Derives profile context (.type domain domainSort) →
      Derives profile ((domain, domainSort) :: context) (.type body codomainSort) →
      profile.Product ⟨domainSort, codomainSort, resultSort⟩ →
      Derives profile context
        (.term function (.pi ⟨domainSort, codomainSort, resultSort⟩ domain body) resultSort) →
      Derives profile context (.term argument domain domainSort) →
      Derives profile context (.term (.app function argument)
        (Term.subst0 argument body) codomainSort)
  | conv {context : SortedCtx SortCode} {subject source target : Term SortCode}
      {sort : SortCode} :
      Derives profile context (.term subject source sort) →
      Conv source target →
      Derives profile context (.type target sort) →
      Derives profile context (.term subject target sort)

theorem Derives.map {Source : Type u} {Target : Type v}
    {sourceProfile : Profile Source} {targetProfile : Profile Target}
    (morphism : Morphism sourceProfile targetProfile) :
    ∀ {context : SortedCtx Source} {judgment : Judgment Source},
      Derives sourceProfile context judgment →
        Derives targetProfile (mapContext morphism.onSort context)
          (Judgment.map morphism.onSort judgment)
  | _, _, .sort known => .sort (morphism.axiom_preserved known)
  | _, _, .pi domain body rule =>
      .pi (domain.map morphism) (body.map morphism)
        (morphism.product_preserved rule)
  | _, _, .ofTerm typed knownAxiom =>
      .ofTerm (typed.map morphism) (morphism.axiom_preserved knownAxiom)
  | _, _, .toTerm typed knownAxiom =>
      .toTerm (typed.map morphism) (morphism.axiom_preserved knownAxiom)
  | _, _, .var found => .var (by
      rw [lookupSorted_map]
      simp [found])
  | _, _, .lam domain bodyType rule body =>
      .lam (domain.map morphism) (bodyType.map morphism)
        (morphism.product_preserved rule) (body.map morphism)
  | _, _, .app domain body rule function argument => by
      simpa [Judgment.map, Term.map, Term.map_subst0] using
        Derives.app (domain.map morphism) (body.map morphism)
        (morphism.product_preserved rule) (function.map morphism)
        (argument.map morphism)
  | _, _, .conv typed converted target =>
      .conv (typed.map morphism) (converted.map morphism.onSort)
        (target.map morphism)

/-! ## Exact connection to the maintained two-sort presentation -/

namespace TwoSort

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile

def ofLFRule (rule : Mettapedia.GSLT.LanguageDef.LFProfile.ProductRule) :
    ProductRule Srt := ⟨rule.domain, rule.codomain, rule.result⟩

def toLFRule (rule : ProductRule Srt) :
    Mettapedia.GSLT.LanguageDef.LFProfile.ProductRule :=
  ⟨rule.domain, rule.codomain, rule.result⟩

@[simp] theorem toLFRule_ofLFRule
    (rule : Mettapedia.GSLT.LanguageDef.LFProfile.ProductRule) :
    toLFRule (ofLFRule rule) = rule := by cases rule; rfl

@[simp] theorem ofLFRule_toLFRule (rule : ProductRule Srt) :
    ofLFRule (toLFRule rule) = rule := by cases rule; rfl

def ofLFProfile (profile : Mettapedia.GSLT.LanguageDef.LFProfile.Profile) :
    Profile Srt where
  Axiom := fun source target => profile.sortAxiom source = some target
  Product := fun rule => toLFRule rule ∈ profile.products

def ofLFTerm : PTerm → Term Srt
  | .var index => .var index
  | .sort sort => .sort sort
  | .pi rule domain body => .pi (ofLFRule rule) (ofLFTerm domain) (ofLFTerm body)
  | .lam sort domain body => .lam sort (ofLFTerm domain) (ofLFTerm body)
  | .app function argument => .app (ofLFTerm function) (ofLFTerm argument)

def toLFTerm : Term Srt → PTerm
  | .var index => .var index
  | .sort sort => .sort sort
  | .pi rule domain body => .pi (toLFRule rule) (toLFTerm domain) (toLFTerm body)
  | .lam sort domain body => .lam sort (toLFTerm domain) (toLFTerm body)
  | .app function argument => .app (toLFTerm function) (toLFTerm argument)

@[simp] theorem toLFTerm_ofLFTerm (term : PTerm) :
    toLFTerm (ofLFTerm term) = term := by induction term <;> simp_all [ofLFTerm, toLFTerm]

@[simp] theorem ofLFTerm_toLFTerm (term : Term Srt) :
    ofLFTerm (toLFTerm term) = term := by induction term <;> simp_all [ofLFTerm, toLFTerm]

@[simp] theorem ofLFTerm_lift (term : PTerm) :
    ∀ amount cutoff, ofLFTerm (PTerm.lift amount cutoff term) =
      Term.lift amount cutoff (ofLFTerm term) := by
  induction term <;> intro amount cutoff <;>
    simp_all [PTerm.lift, Term.lift, ofLFTerm]

@[simp] theorem ofLFTerm_subst (term : PTerm) :
    ∀ target replacement, ofLFTerm (PTerm.subst target replacement term) =
      Term.subst target (ofLFTerm replacement) (ofLFTerm term) := by
  induction term with
  | var index =>
      intro target replacement
      by_cases same : index = target
      · simp [PTerm.subst, Term.subst, ofLFTerm, same]
      · by_cases earlier : target < index <;>
          simp [PTerm.subst, Term.subst, ofLFTerm, same, earlier]
  | sort sort => intro target replacement; rfl
  | pi rule domain body ihDomain ihBody =>
      intro target replacement
      simp [PTerm.subst, Term.subst, ofLFTerm, ihDomain, ihBody]
  | lam sort domain body ihDomain ihBody =>
      intro target replacement
      simp [PTerm.subst, Term.subst, ofLFTerm, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro target replacement
      simp [PTerm.subst, Term.subst, ofLFTerm, ihFunction, ihArgument]

def ofLFContext (context : Mettapedia.GSLT.Dedukti.SortedCtx) : SortedCtx Srt :=
  match context with
  | [] => []
  | (term, sort) :: rest => (ofLFTerm term, sort) :: ofLFContext rest

theorem ofLFContext_eq_map (context : Mettapedia.GSLT.Dedukti.SortedCtx) :
    ofLFContext context = context.map fun entry => (ofLFTerm entry.1, entry.2) := by
  induction context with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨term, sort⟩
      simp [ofLFContext, ih]

def ofLFJudgment : Mettapedia.GSLT.Dedukti.Judgment → Judgment Srt
  | .type subject sort => .type (ofLFTerm subject) sort
  | .term subject type sort => .term (ofLFTerm subject) (ofLFTerm type) sort

theorem lookupSorted_ofLFContext
    (context : Mettapedia.GSLT.Dedukti.SortedCtx) (index : Nat) :
    lookupSorted (ofLFContext context) index =
      (Mettapedia.GSLT.Dedukti.lookupSorted context index).map fun entry =>
        (ofLFTerm entry.1, entry.2) := by
  rw [ofLFContext_eq_map]
  simp only [lookupSorted, Mettapedia.GSLT.Dedukti.lookupSorted,
    List.getElem?_map, Option.map_map]
  cases context[index]? with
  | none => rfl
  | some entry =>
      rcases entry with ⟨term, sort⟩
      simp

theorem ofLFStep {source target : PTerm}
    (step : Mettapedia.GSLT.Dedukti.PTerm.Step source target) :
    Step (ofLFTerm source) (ofLFTerm target) := by
  induction step with
  | beta level domain body argument =>
      simpa [ofLFTerm, PTerm.subst0, Term.subst0] using
        (Step.beta level (ofLFTerm domain) (ofLFTerm body) (ofLFTerm argument))
  | piDomain step ih => exact .piDomain ih
  | piBody step ih => exact .piBody ih
  | lamDomain step ih => exact .lamDomain ih
  | lamBody step ih => exact .lamBody ih
  | appFunction step ih => exact .appFunction ih
  | appArgument step ih => exact .appArgument ih

theorem ofLFConv {source target : PTerm}
    (converted : Mettapedia.GSLT.Dedukti.PTerm.Conv source target) :
    Conv (ofLFTerm source) (ofLFTerm target) := by
  induction converted with
  | rel _ _ step => exact .rel _ _ (ofLFStep step)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-- Every derivation in the maintained two-sort calculus is a derivation of
its exact generic instance. -/
theorem ofLFDerives
    {profile : Mettapedia.GSLT.LanguageDef.LFProfile.Profile} :
    ∀ {context : Mettapedia.GSLT.Dedukti.SortedCtx}
      {judgment : Mettapedia.GSLT.Dedukti.Judgment},
      Mettapedia.GSLT.Dedukti.Derives profile context judgment →
        Derives (ofLFProfile profile) (ofLFContext context) (ofLFJudgment judgment)
  | _, _, .sort known => .sort known
  | _, _, .pi domain body rule =>
      .pi (ofLFDerives domain) (ofLFDerives body) rule
  | _, _, .ofTerm typed knownAxiom => .ofTerm (ofLFDerives typed) knownAxiom
  | _, _, .toTerm typed knownAxiom => .toTerm (ofLFDerives typed) knownAxiom
  | _, _, .var found => .var (by
      rw [lookupSorted_ofLFContext]
      simp [found])
  | _, _, .lam domain bodyType rule body =>
      .lam (ofLFDerives domain) (ofLFDerives bodyType) rule (ofLFDerives body)
  | _, _, .app domain body rule function argument => by
      simpa [ofLFJudgment, ofLFTerm, PTerm.subst0, Term.subst0,
        ofLFTerm_subst] using
        Derives.app (ofLFDerives domain) (ofLFDerives body) rule
          (ofLFDerives function) (ofLFDerives argument)
  | _, _, .conv typed converted target =>
      .conv (ofLFDerives typed) (ofLFConv converted) (ofLFDerives target)

@[simp] theorem toLFTerm_lift (term : Term Srt) :
    ∀ amount cutoff, toLFTerm (Term.lift amount cutoff term) =
      PTerm.lift amount cutoff (toLFTerm term) := by
  induction term <;> intro amount cutoff <;>
    simp_all [Term.lift, PTerm.lift, toLFTerm]

@[simp] theorem toLFTerm_subst (term : Term Srt) :
    ∀ target replacement, toLFTerm (Term.subst target replacement term) =
      PTerm.subst target (toLFTerm replacement) (toLFTerm term) := by
  induction term with
  | var index =>
      intro target replacement
      by_cases same : index = target
      · simp [Term.subst, PTerm.subst, toLFTerm, same]
      · by_cases earlier : target < index <;>
          simp [Term.subst, PTerm.subst, toLFTerm, same, earlier]
  | sort sort => intro target replacement; rfl
  | pi rule domain body ihDomain ihBody =>
      intro target replacement
      simp [Term.subst, PTerm.subst, toLFTerm, ihDomain, ihBody]
  | lam sort domain body ihDomain ihBody =>
      intro target replacement
      simp [Term.subst, PTerm.subst, toLFTerm, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro target replacement
      simp [Term.subst, PTerm.subst, toLFTerm, ihFunction, ihArgument]

def toLFContext (context : SortedCtx Srt) : Mettapedia.GSLT.Dedukti.SortedCtx :=
  match context with
  | [] => []
  | (term, sort) :: rest => (toLFTerm term, sort) :: toLFContext rest

def toLFJudgment : Judgment Srt → Mettapedia.GSLT.Dedukti.Judgment
  | .type subject sort => .type (toLFTerm subject) sort
  | .term subject typeExpr sort => .term (toLFTerm subject) (toLFTerm typeExpr) sort

@[simp] theorem toLFContext_ofLFContext
    (context : Mettapedia.GSLT.Dedukti.SortedCtx) :
    toLFContext (ofLFContext context) = context := by
  induction context with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨term, sort⟩
      simp [ofLFContext, toLFContext, ih]

@[simp] theorem toLFJudgment_ofLFJudgment
    (judgment : Mettapedia.GSLT.Dedukti.Judgment) :
    toLFJudgment (ofLFJudgment judgment) = judgment := by
  cases judgment <;> simp [ofLFJudgment, toLFJudgment]

theorem toLFContext_eq_map (context : SortedCtx Srt) :
    toLFContext context = context.map fun entry => (toLFTerm entry.1, entry.2) := by
  induction context with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨term, sort⟩
      simp [toLFContext, ih]

theorem lookupSorted_toLFContext (context : SortedCtx Srt) (index : Nat) :
    Mettapedia.GSLT.Dedukti.lookupSorted (toLFContext context) index =
      (lookupSorted context index).map fun entry => (toLFTerm entry.1, entry.2) := by
  rw [toLFContext_eq_map]
  simp only [lookupSorted, Mettapedia.GSLT.Dedukti.lookupSorted,
    List.getElem?_map, Option.map_map]
  cases context[index]? with
  | none => rfl
  | some entry =>
      rcases entry with ⟨term, sort⟩
      simp

theorem toLFStep {source target : Term Srt} (step : Step source target) :
    Mettapedia.GSLT.Dedukti.PTerm.Step (toLFTerm source) (toLFTerm target) := by
  induction step with
  | beta level domain body argument =>
      simpa [toLFTerm, Term.subst0, PTerm.subst0] using
        (Mettapedia.GSLT.Dedukti.PTerm.Step.beta level (toLFTerm domain)
          (toLFTerm body) (toLFTerm argument))
  | piDomain step ih => exact .piDomain ih
  | piBody step ih => exact .piBody ih
  | lamDomain step ih => exact .lamDomain ih
  | lamBody step ih => exact .lamBody ih
  | appFunction step ih => exact .appFunction ih
  | appArgument step ih => exact .appArgument ih

theorem toLFConv {source target : Term Srt} (converted : Conv source target) :
    Mettapedia.GSLT.Dedukti.PTerm.Conv (toLFTerm source) (toLFTerm target) := by
  induction converted with
  | rel _ _ step => exact .rel _ _ (toLFStep step)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-- Conversely, a derivation of a generic two-sort instance is a derivation
of the maintained presentation. -/
theorem toLFDerives
    {profile : Mettapedia.GSLT.LanguageDef.LFProfile.Profile} :
    ∀ {context : SortedCtx Srt} {judgment : Judgment Srt},
      Derives (ofLFProfile profile) context judgment →
        Mettapedia.GSLT.Dedukti.Derives profile (toLFContext context)
          (toLFJudgment judgment)
  | _, _, .sort known => .sort known
  | _, _, .pi domain body rule =>
      .pi (toLFDerives domain) (toLFDerives body) rule
  | _, _, .ofTerm typed knownAxiom => .ofTerm (toLFDerives typed) knownAxiom
  | _, _, .toTerm typed knownAxiom => .toTerm (toLFDerives typed) knownAxiom
  | _, _, .var found => .var (by
      rw [lookupSorted_toLFContext]
      simp [found])
  | _, _, .lam domain bodyType rule body =>
      .lam (toLFDerives domain) (toLFDerives bodyType) rule (toLFDerives body)
  | _, _, .app domain body rule function argument => by
      simpa [toLFJudgment, toLFTerm, Term.subst0, PTerm.subst0,
        toLFTerm_subst] using
        Mettapedia.GSLT.Dedukti.Derives.app (toLFDerives domain)
          (toLFDerives body) rule (toLFDerives function) (toLFDerives argument)
  | _, _, .conv typed converted target =>
      .conv (toLFDerives typed) (toLFConv converted) (toLFDerives target)

/-- Exact correspondence with the maintained two-sort calculus. -/
theorem derives_iff
    {profile : Mettapedia.GSLT.LanguageDef.LFProfile.Profile}
    {context : Mettapedia.GSLT.Dedukti.SortedCtx}
    {judgment : Mettapedia.GSLT.Dedukti.Judgment} :
    Mettapedia.GSLT.Dedukti.Derives profile context judgment ↔
      Derives (ofLFProfile profile) (ofLFContext context) (ofLFJudgment judgment) := by
  constructor
  · exact ofLFDerives
  · intro derived
    simpa using toLFDerives derived

end TwoSort

#print axioms Derives.map
#print axioms TwoSort.ofLFDerives
#print axioms TwoSort.derives_iff

end Mettapedia.GSLT.Dedukti.GenericPureTypeSystem
