import Mettapedia.GSLT.Dedukti.PureTypeSystem

/-!
# A sound type inference procedure for sorted pure type systems

Type inference for the sorted presentation of a pure type system, for any
profile (`inferSort`, `inferTerm`). Conversion is decided by comparing
leftmost-outermost normal forms computed within a step budget (`normalize`);
an exhausted budget makes the procedure abstain, never accept.

* **Soundness.** Every inferred judgment is derivable (`inferSort_sound`,
  `inferTerm_sound`). Each rule's premises are produced by recursive calls,
  and every conversion used is witnessed by the reduction sequences the
  normalizer actually performed (`normalize_conv`).
* **No completeness is claimed.** Normalization need not terminate in every
  profile, so a refusal says nothing about derivability. Searching for a
  proof and checking a supplied term remain different operations: this
  procedure checks a supplied term.

The procedure is computable and reduces in the kernel, so a derivation of a
concrete judgment can be obtained by evaluating it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)

namespace PTerm

/-- One leftmost-outermost beta step, if the term has a redex. -/
def step? : PTerm → Option PTerm
  | .app (.lam _ _ body) argument => some (subst0 argument body)
  | .app function argument =>
      match step? function with
      | some function' => some (.app function' argument)
      | none => (step? argument).map (.app function)
  | .pi rule domain body =>
      match step? domain with
      | some domain' => some (.pi rule domain' body)
      | none => (step? body).map (.pi rule domain)
  | .lam level domain body =>
      match step? domain with
      | some domain' => some (.lam level domain' body)
      | none => (step? body).map (.lam level domain)
  | .var _ => none
  | .sort _ => none

theorem step?_sound : ∀ {source target : PTerm}, step? source = some target → Step source target
  | .app (.lam level domain body) argument, target, found => by
      simp only [step?, Option.some.injEq] at found
      subst found
      exact .beta level domain body argument
  | .app (.var index) argument, target, found => by
      simp only [step?, Option.map_eq_some_iff] at found
      obtain ⟨argument', stepped, rfl⟩ := found
      exact .appArgument (step?_sound stepped)
  | .app (.sort level) argument, target, found => by
      simp only [step?, Option.map_eq_some_iff] at found
      obtain ⟨argument', stepped, rfl⟩ := found
      exact .appArgument (step?_sound stepped)
  | .app (.pi rule domain body) argument, target, found => by
      simp only [step?] at found
      split at found
      · rename_i function' stepped
        simp only [Option.some.injEq] at found
        subst found
        exact .appFunction (step?_sound stepped)
      · obtain ⟨argument', stepped, rfl⟩ := Option.map_eq_some_iff.mp found
        exact .appArgument (step?_sound stepped)
  | .app (.app function inner) argument, target, found => by
      simp only [step?] at found
      split at found
      · rename_i function' stepped
        simp only [Option.some.injEq] at found
        subst found
        exact .appFunction (step?_sound stepped)
      · obtain ⟨argument', stepped, rfl⟩ := Option.map_eq_some_iff.mp found
        exact .appArgument (step?_sound stepped)
  | .pi rule domain body, target, found => by
      simp only [step?] at found
      split at found
      · rename_i domain' stepped
        simp only [Option.some.injEq] at found
        subst found
        exact .piDomain (step?_sound stepped)
      · obtain ⟨body', stepped, rfl⟩ := Option.map_eq_some_iff.mp found
        exact .piBody (step?_sound stepped)
  | .lam level domain body, target, found => by
      simp only [step?] at found
      split at found
      · rename_i domain' stepped
        simp only [Option.some.injEq] at found
        subst found
        exact .lamDomain (step?_sound stepped)
      · obtain ⟨body', stepped, rfl⟩ := Option.map_eq_some_iff.mp found
        exact .lamBody (step?_sound stepped)
  | .var _, _, found => by simp [step?] at found
  | .sort _, _, found => by simp [step?] at found

/-- Run leftmost-outermost reduction for at most the given number of steps. -/
def normalize : Nat → PTerm → PTerm
  | 0, term => term
  | budget + 1, term =>
      match step? term with
      | none => term
      | some reduced => normalize budget reduced

theorem normalize_conv : ∀ (budget : Nat) (term : PTerm), Conv term (normalize budget term)
  | 0, term => .refl _
  | budget + 1, term => by
      simp only [normalize]
      split
      · exact .refl _
      · rename_i reduced stepped
        exact .trans _ _ _ (.rel _ _ (step?_sound stepped)) (normalize_conv budget reduced)

/-- Compare normal forms within a budget. -/
def convertible (budget : Nat) (left right : PTerm) : Bool :=
  decide (normalize budget left = normalize budget right)

theorem convertible_sound {budget : Nat} {left right : PTerm}
    (same : convertible budget left right = true) : Conv left right := by
  have equal : normalize budget left = normalize budget right := of_decide_eq_true same
  exact .trans _ _ _ (normalize_conv budget left)
    (equal ▸ .symm _ _ (normalize_conv budget right))

end PTerm

namespace Checker

/-- Find a product rule of the profile with the given domain and codomain
sorts. -/
def findRule (profile : Profile) (domainSort codomainSort : Srt) : Option ProductRule :=
  profile.products.find? fun rule => rule.domain = domainSort && rule.codomain = codomainSort

theorem findRule_mem {profile : Profile} {domainSort codomainSort : Srt} {rule : ProductRule}
    (found : findRule profile domainSort codomainSort = some rule) :
    rule ∈ profile.products ∧ rule.domain = domainSort ∧ rule.codomain = codomainSort := by
  have member := List.mem_of_find?_eq_some found
  have selected := List.find?_some found
  simp only [Bool.and_eq_true, decide_eq_true_eq] at selected
  exact ⟨member, selected⟩

/-- Membership of a product rule, decided. -/
def hasRule (profile : Profile) (rule : ProductRule) : Bool :=
  decide (rule ∈ profile.products)

mutual

/-- Infer the sort of a type. -/
def inferSort (profile : Profile) (budget : Nat) : Nat → SortedCtx → PTerm → Option Srt
  | 0, _, _ => none
  | _ + 1, _, .sort level => profile.sortAxiom level
  | fuel + 1, context, .pi rule domain body =>
      if inferSort profile budget fuel context domain = some rule.domain ∧
          inferSort profile budget fuel ((domain, rule.domain) :: context) body = some rule.codomain ∧
          hasRule profile rule = true then
        some rule.result
      else none
  | fuel + 1, context, subject =>
      match inferTerm profile budget fuel context subject with
      | none => none
      | some (type, above) =>
          match PTerm.normalize budget type with
          | .sort level => if profile.sortAxiom level = some above then some level else none
          | _ => none

/-- Infer the type of a term, with the sort of that type. -/
def inferTerm (profile : Profile) (budget : Nat) : Nat → SortedCtx → PTerm → Option (PTerm × Srt)
  | 0, _, _ => none
  | _ + 1, context, .var index => lookupSorted context index
  | _ + 1, _, .sort level =>
      match profile.sortAxiom level with
      | none => none
      | some above =>
          match profile.sortAxiom above with
          | none => none
          | some top => some (.sort above, top)
  | fuel + 1, context, .pi rule domain body =>
      match inferSort profile budget fuel context (.pi rule domain body) with
      | none => none
      | some level =>
          match profile.sortAxiom level with
          | none => none
          | some above => some (.sort level, above)
  | fuel + 1, context, .lam level domain body =>
      if inferSort profile budget fuel context domain = some level then
        match inferTerm profile budget fuel ((domain, level) :: context) body with
        | none => none
        | some (bodyType, codomainSort) =>
            if inferSort profile budget fuel ((domain, level) :: context) bodyType =
                some codomainSort then
              match findRule profile level codomainSort with
              | none => none
              | some rule => some (.pi rule domain bodyType, rule.result)
            else none
      else none
  | fuel + 1, context, .app function argument =>
      match inferTerm profile budget fuel context function with
      | none => none
      | some (functionType, resultSort) =>
          match PTerm.normalize budget functionType with
          | .pi rule domain bodyType =>
              if rule.result = resultSort ∧
                  inferSort profile budget fuel context domain = some rule.domain ∧
                  inferSort profile budget fuel ((domain, rule.domain) :: context) bodyType =
                    some rule.codomain ∧
                  hasRule profile rule = true then
                match inferTerm profile budget fuel context argument with
                | none => none
                | some (argumentType, argumentSort) =>
                    if argumentSort = rule.domain ∧
                        PTerm.convertible budget argumentType domain = true then
                      some (PTerm.subst0 argument bodyType, rule.codomain)
                    else none
              else none
          | _ => none

end

theorem hasRule_mem {profile : Profile} {rule : ProductRule}
    (found : hasRule profile rule = true) : rule ∈ profile.products :=
  of_decide_eq_true found

theorem conv_to_sort {profile : Profile} {context : SortedCtx} {subject type : PTerm}
    {above level : Srt} (budget : Nat)
    (derived : Derives profile context (.term subject type above))
    (normal : PTerm.normalize budget type = .sort level)
    (axiom' : profile.sortAxiom level = some above) :
    Derives profile context (.term subject (.sort level) above) :=
  .conv derived (normal ▸ PTerm.normalize_conv budget type) (.sort axiom')

/-- **Soundness of inference.** Every inferred judgment is derivable. -/
theorem sound (profile : Profile) (budget : Nat) : ∀ fuel : Nat,
    (∀ context type sort, inferSort profile budget fuel context type = some sort →
      Derives profile context (.type type sort)) ∧
    (∀ context subject type sort, inferTerm profile budget fuel context subject = some (type, sort) →
      Derives profile context (.term subject type sort))
  | 0 => ⟨fun _ _ _ found => by simp [inferSort] at found,
      fun _ _ _ _ found => by simp [inferTerm] at found⟩
  | fuel + 1 => by
      obtain ⟨sortSound, termSound⟩ := sound profile budget fuel
      have viaTerm : ∀ context subject sort,
          (match inferTerm profile budget fuel context subject with
            | none => none
            | some (type, above) =>
                match PTerm.normalize budget type with
                | .sort level => if profile.sortAxiom level = some above then some level else none
                | _ => none) = some sort →
          Derives profile context (.type subject sort) := by
        intro context subject sort found
        split at found
        · simp at found
        · rename_i type above inferred
          split at found
          · rename_i level normal
            split at found
            · rename_i axiom'
              simp only [Option.some.injEq] at found
              subst found
              exact .ofTerm (conv_to_sort budget (termSound _ _ _ _ inferred) normal axiom') axiom'
            · simp at found
          · simp at found
      constructor
      · intro context type sort found
        cases type with
        | sort level =>
            exact .sort found
        | pi rule domain body =>
            simp only [inferSort] at found
            split at found
            · rename_i conditions
              obtain ⟨domainFound, bodyFound, ruleFound⟩ := conditions
              simp only [Option.some.injEq] at found
              subst found
              obtain ⟨d, c, r⟩ := rule
              exact .pi (sortSound _ _ _ domainFound) (sortSound _ _ _ bodyFound) (hasRule_mem ruleFound)
            · simp at found
        | var index => exact viaTerm _ _ _ found
        | lam level domain body => exact viaTerm _ _ _ found
        | app function argument => exact viaTerm _ _ _ found
      · intro context subject type sort found
        cases subject with
        | var index => exact .var found
        | sort level =>
            simp only [inferTerm] at found
            split at found
            · simp at found
            · rename_i above first
              split at found
              · simp at found
              · rename_i top second
                simp only [Option.some.injEq, Prod.mk.injEq] at found
                obtain ⟨rfl, rfl⟩ := found
                exact .toTerm (.sort first) second
        | pi rule domain body =>
            simp only [inferTerm] at found
            split at found
            · simp at found
            · rename_i level formed
              split at found
              · simp at found
              · rename_i above axiom'
                simp only [Option.some.injEq, Prod.mk.injEq] at found
                obtain ⟨rfl, rfl⟩ := found
                exact .toTerm (sortSound _ _ _ formed) axiom'
        | lam level domain body =>
            simp only [inferTerm] at found
            split at found
            · rename_i domainFound
              split at found
              · simp at found
              · rename_i bodyType codomainSort bodyFound
                split at found
                · rename_i bodyTypeFound
                  split at found
                  · simp at found
                  · rename_i rule ruleFound
                    simp only [Option.some.injEq, Prod.mk.injEq] at found
                    obtain ⟨rfl, rfl⟩ := found
                    obtain ⟨member, domainSame, codomainSame⟩ := findRule_mem ruleFound
                    obtain ⟨d, c, r⟩ := rule
                    simp only at domainSame codomainSame
                    subst domainSame codomainSame
                    exact .lam (sortSound _ _ _ domainFound) (sortSound _ _ _ bodyTypeFound) member
                      (termSound _ _ _ _ bodyFound)
                · simp at found
            · simp at found
        | app function argument =>
            simp only [inferTerm] at found
            split at found
            · simp at found
            · rename_i functionType resultSort functionFound
              split at found
              · rename_i rule domain bodyType normal
                split at found
                · rename_i conditions
                  obtain ⟨resultSame, domainFound, bodyFound, ruleFound⟩ := conditions
                  split at found
                  · simp at found
                  · rename_i argumentType argumentSort argumentFound
                    split at found
                    · rename_i argumentConditions
                      obtain ⟨argumentSame, converted⟩ := argumentConditions
                      simp only [Option.some.injEq, Prod.mk.injEq] at found
                      obtain ⟨rfl, rfl⟩ := found
                      subst resultSame argumentSame
                      obtain ⟨d, c, r⟩ := rule
                      have domainDerived := sortSound _ _ _ domainFound
                      have bodyDerived := sortSound _ _ _ bodyFound
                      have member := hasRule_mem ruleFound
                      have productFormed : Derives profile context
                          (.type (.pi ⟨d, c, r⟩ domain bodyType) r) :=
                        .pi domainDerived bodyDerived member
                      have functionDerived : Derives profile context
                          (.term function (.pi ⟨d, c, r⟩ domain bodyType) r) :=
                        .conv (termSound _ _ _ _ functionFound)
                          (normal ▸ PTerm.normalize_conv budget functionType) productFormed
                      have argumentDerived : Derives profile context (.term argument domain d) :=
                        .conv (termSound _ _ _ _ argumentFound)
                          (PTerm.convertible_sound converted) domainDerived
                      exact .app domainDerived bodyDerived member functionDerived argumentDerived
                    · simp at found
                · simp at found
              · simp at found

theorem inferTerm_sound {profile : Profile} {budget fuel : Nat} {context : SortedCtx}
    {subject type : PTerm} {sort : Srt}
    (found : inferTerm profile budget fuel context subject = some (type, sort)) :
    Derives profile context (.term subject type sort) :=
  (sound profile budget fuel).2 _ _ _ _ found

theorem inferSort_sound {profile : Profile} {budget fuel : Nat} {context : SortedCtx}
    {type : PTerm} {sort : Srt}
    (found : inferSort profile budget fuel context type = some sort) :
    Derives profile context (.type type sort) :=
  (sound profile budget fuel).1 _ _ _ found

end Checker

end Mettapedia.GSLT.Dedukti
