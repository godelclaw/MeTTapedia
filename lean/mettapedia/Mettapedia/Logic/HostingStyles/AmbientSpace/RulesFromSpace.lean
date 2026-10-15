import Mettapedia.Logic.HostingStyles.AmbientSpace.Hosting

/-!
# What the family assumes of its evaluators: the rules come from the space

A presented candidate names its evaluator.  Respecting the static equivalence
does not by itself exclude an evaluator chosen from the sources; for an
evaluator of the run premise the further property is `RulesFromSpace`.  Its
analogue for a family indexed by a space is `FamilyRulesFromSpace`: **the
member at a space that stores no atom answers the premise of the root step
with nothing.**

* The family that matches in its space has it
  (`ambientEvaluator_rulesFromSpace`), and an evaluator of the run premise
  that reads such a family at the space that the run binds takes its rules
  from the space (`rulesFromSpace_of_family`); the matching evaluator is one
  (`matchingEvaluator_rulesFromSpace_of_family`).
* **Negative**: the family of a listing (`listedFamily`).  Every member
  answers with the reducts that a listing of the source gives, whatever its
  space is.  Every member respects the static equivalence
  (`listedFamily_respectsStatics`) and hosts the listed theory on terms, at
  every space (`listedMap_hosting`); the family of the tables whose rules
  determine their right sides hosts, at the empty space, the class that the
  family of this delivery hosts at the spaces of the tables
  (`determinedFamily_hostOf_firstOrderTabular`).  It does not take its rules
  from the space (`listedFamily_not_rulesFromSpace`,
  `determinedFamily_not_rulesFromSpace`).

So what separates the two families is the property, and neither hosting nor
the static equivalence (`rulesFromSpace_separates`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory rewritingTheory)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-! ## The property -/

/-- **A family of evaluators indexed by a space takes its rules from the
space**: the member at a space that stores no atom answers the premise of the
root step with nothing. -/
def FamilyRulesFromSpace (family : Pattern → BasePremiseEvaluator) : Prop :=
  ∀ space : Pattern, storedAtoms (contract space) = [] →
    ∀ (lang : LanguageDef) (bindings : Bindings), family space lang bindings rootPremise = []

/-- **Positive**: the family that matches in its space. -/
theorem ambientEvaluator_rulesFromSpace : FamilyRulesFromSpace ambientEvaluator :=
  fun _ empty lang bindings => ambientEvaluator_of_stores_nothing empty lang bindings rootPremise

/-- **An evaluator of the run premise that reads a family at the space that
the run binds takes its rules from the space**, when the family does. -/
theorem rulesFromSpace_of_family {evaluator : BasePremiseEvaluator}
    {family : Pattern → BasePremiseEvaluator}
    (reads : ∀ (lang : LanguageDef) (bindings : Bindings),
      evaluator lang bindings runPremise =
        family (applyBindings bindings (.fvar "space")) lang bindings rootPremise)
    (fromSpace : FamilyRulesFromSpace family) : RulesFromSpace evaluator :=
  fun lang bindings empty => (reads lang bindings).trans (fromSpace _ empty lang bindings)

/-- The matching evaluator takes its rules from the space because the family
it reads does. -/
theorem matchingEvaluator_rulesFromSpace_of_family : RulesFromSpace matchingEvaluator :=
  rulesFromSpace_of_family matchingEvaluator_run_eq_ambient ambientEvaluator_rulesFromSpace

/-! ## The family of a listing -/

/-- **The family of a listing.**  Every member answers the premise of the
root step with the numerals of the reducts of the term whose numeral the
subject is.  The rules are the steps of the listed theory; no member reads
its space. -/
noncomputable def listedFamily {Source : Type} (code : Source → Nat) (next : Source → List Source) :
    Pattern → BasePremiseEvaluator := fun _ _ bindings premise =>
  match premise with
  | .relationQuery "AmbientStep" [subject, .fvar answer] =>
      stepAnswers code next bindings subject answer
  | _ => []

/-- All members of the family of a listing are one evaluator. -/
theorem listedFamily_constant {Source : Type} (code : Source → Nat) (next : Source → List Source)
    (first second : Pattern) : listedFamily code next first = listedFamily code next second :=
  rfl

/-- **Every member of the family of a listing respects the static
equivalence of the presentation.** -/
theorem listedFamily_respectsStatics {Source : Type} (code : Source → Nat)
    (next : Source → List Source) (space : Pattern) :
    RespectsStatics (listedFamily code next space) ambient := by
  intro premise member first second related result answered
  have contractions : BindingsRelated (fun left right => contract left = contract right) first
      second := related.mono fun _ _ equivalent => (ambient_quoteDropOnly.equiv equivalent).1
  rcases ambient_premises premise member with rfl | ⟨source, target, rfl⟩
  · have same := contract_applyBindings_congr contractions (.fvar "subject") rfl
    have answers : result ∈ stepAnswers code next first (.fvar "subject") "answer" := answered
    obtain ⟨reduct, rfl, other⟩ := stepAnswers_related code next "answer" same answers
    exact ⟨_, other, .cons ⟨rfl, .refl _⟩ related⟩
  · simp [listedFamily] at answered

/-- **Negative**: the family of a listing does not take its rules from the
space.  Where the listed theory has a step, the member at the empty space
answers. -/
theorem listedFamily_not_rulesFromSpace {source : GSLT.{0}} (listing : StepListing source)
    {term reduct : source.Term} (step : source.rewrites term reduct) :
    ¬ FamilyRulesFromSpace (listedFamily listing.code listing.next) := by
  intro fromSpace
  have silent := fromSpace emptySpace (by decide) ambient
    [("subject", numeral (listing.code term))]
  have answered : (("answer", numeral (listing.code reduct)) ::
      [("subject", numeral (listing.code term))]) ∈
      listedFamily listing.code listing.next emptySpace ambient
        [("subject", numeral (listing.code term))] rootPremise := by
    show _ ∈ stepAnswers listing.code listing.next _ (.fvar "subject") "answer"
    rw [stepAnswers_eq listing.injective listing.next "answer" (term := term)
      (by
        rw [show applyBindings [("subject", numeral (listing.code term))] (.fvar "subject") =
          numeral (listing.code term) by simp [applyBindings], contract_numeral])]
    exact List.mem_map.mpr ⟨reduct, (listing.branches term reduct).mp step, rfl⟩
  rw [silent] at answered
  cases answered

/-! ## It hosts the listed theory at every space -/

/-- A numeral, as a closed atom of the presentation. -/
def numeralTerm (count : Nat) : Contexts.Term ambient AtomsReduce.closedAtom :=
  ⟨numeral count, numeral_wellSorted_of ambient_carriesAtoms [] count⟩

/-- An application of a constructor other than the equation constructor and
the unit atom matches no numeral. -/
theorem numeral_not_matched {label : String} (notEquation : label ≠ "=")
    (notUnit : label ≠ "prime-unit") {parameters : List Pattern} {count : Nat}
    {bindings : Bindings} : bindings ∉ matchPattern (.apply label parameters) (numeral count) := by
  intro matched
  obtain ⟨arguments, shape, -⟩ := eq_apply_of_matched matched
  cases count with
  | zero =>
      simp only [numeral, unitAtom, Pattern.apply.injEq] at shape
      exact notUnit shape.1.symm
  | succ count =>
      simp only [numeral, Pattern.apply.injEq] at shape
      exact notEquation shape.1.symm

/-- **A numeral steps by an answer of the evaluator alone**, in the ambient
presentation and under every evaluator of its premises: it is no application,
abstraction, product or dropping. -/
theorem numeral_stepAt_inv {base : BasePremiseEvaluator} {fuel : Nat} {count : Nat}
    {target : Pattern} (step : StepAt base ambient fuel (numeral count) target) :
    ∃ final ∈ base ambient [("subject", numeral count)] rootPremise,
      target = applyRuleBindings rootRule final := by
  cases fuel with
  | zero => cases step
  | succ fuel =>
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [ambient_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd matched (numeral_not_matched (label := "App") (by decide) (by decide))
      · exact absurd matched (numeral_not_matched (label := "App") (by decide) (by decide))
      · exact absurd matched (numeral_not_matched (label := "App") (by decide) (by decide))
      · exact absurd matched (numeral_not_matched (label := "Pi") (by decide) (by decide))
      · exact absurd matched (numeral_not_matched (label := "Pi") (by decide) (by decide))
      · exact absurd matched (numeral_not_matched (label := "Lam") (by decide) (by decide))
      · exact absurd matched (numeral_not_matched (label := "Lam") (by decide) (by decide))
      · exact absurd matched (numeral_not_matched (label := "prime-drop") (by decide) (by decide))
      · have bound : initial = [("subject", numeral count)] :=
          mem_matchPattern_fvar.mp
            (show initial ∈ matchPattern (.fvar "subject") (numeral count) from matched)
        subst bound
        have premises' : PremisesAt base ambient fuel [("subject", numeral count)] [rootPremise]
            final := premises
        cases premises' with
        | cons first rest =>
            cases rest
            cases first with
            | relationQuery answered => exact ⟨_, answered, rfl⟩

/-- **A listed theory, in the member of the family of its listing at a
space**: a term is read as the numeral of its number. -/
noncomputable def listedMap {source : GSLT.{0}} (listing : StepListing source) (space : Pattern) :
    ContextMap source.termsAlone
      (contextTheory (listedFamily listing.code listing.next space) ambientPresentation) :=
  ContextMap.ofTerms (source := source)
    (target := contextTheory (listedFamily listing.code listing.next space) ambientPresentation)
    AtomsReduce.closedAtom (fun term => numeralTerm (listing.code term))
    (fun {first second} related => by
      rw [listing.discrete first second related]
      exact Relation.EqvGen.refl _)

/-- The answers of the family of a listing for the numeral of a term. -/
theorem listedFamily_numeral {source : GSLT.{0}} (listing : StepListing source) (space : Pattern)
    (term : source.Term) :
    listedFamily listing.code listing.next space ambient
        [("subject", numeral (listing.code term))] rootPremise =
      (listing.next term).map fun reduct =>
        ("answer", numeral (listing.code reduct)) :: [("subject", numeral (listing.code term))] := by
  show stepAnswers listing.code listing.next _ (.fvar "subject") "answer" = _
  exact stepAnswers_eq listing.injective listing.next "answer" (term := term)
    (by
      rw [show applyBindings [("subject", numeral (listing.code term))] (.fvar "subject") =
        numeral (listing.code term) by simp [applyBindings], contract_numeral])

/-- **Every member of the family of a listing hosts the listed theory on
terms**, whatever its space is. -/
theorem listedMap_hosting {source : GSLT.{0}} (listing : StepListing source) (space : Pattern) :
    (listedMap listing space).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := source)
    (target := contextTheory (listedFamily listing.code listing.next space) ambientPresentation)
    AtomsReduce.closedAtom (fun term => numeralTerm (listing.code term))
    (fun {first second} related => by
      rw [listing.discrete first second related]
      exact Relation.EqvGen.refl _)).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    have same := ambient_quoteDropOnly.contract_eq related
    have unfolded : contract (numeral (listing.code first)) =
        contract (numeral (listing.code second)) := same
    rw [contract_numeral, contract_numeral] at unfolded
    rw [listing.injective (numeral_injective unfolded)]
  · intro first next step
    refine ⟨numeralTerm (listing.code first), numeralTerm (listing.code next),
      Relation.EqvGen.refl _, ⟨1, ?_⟩, Relation.EqvGen.refl _⟩
    show StepAt (listedFamily listing.code listing.next space) ambient 1
      (numeral (listing.code first)) (numeral (listing.code next))
    refine stepAt_of_rule (rule := rootRule) (by simp [ambient_rewrites])
      (initial := [("subject", numeral (listing.code first))])
      (final := [("answer", numeral (listing.code next)),
        ("subject", numeral (listing.code first))]) ?_ ?_ ?_
    · simp [rootRule, matchPattern]
    · refine .cons (.relationQuery ?_) (.nil _)
      show _ ∈ listedFamily listing.code listing.next space ambient
        [("subject", numeral (listing.code first))] rootPremise
      rw [listedFamily_numeral]
      exact List.mem_map.mpr ⟨next, (listing.branches first next).mp step, rfl⟩
    · simp [applyRuleBindings, rootRule, applyBindings]
  · rintro first next ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩
    obtain rfl : redex = numeralTerm (listing.code first) :=
      eq_of_related_of_dropFree (show resultIn unquotedSorts (.base "Atom") = true by decide)
        (contract_numeral _) (tokens_numeral (by decide) (by decide) _) before
    obtain ⟨final, answered, shape⟩ := numeral_stepAt_inv fired
    rw [listedFamily_numeral] at answered
    obtain ⟨reduct, member, rfl⟩ := List.mem_map.mp answered
    refine ⟨reduct, (listing.branches first reduct).mpr member, ?_⟩
    have image : contractum = numeralTerm (listing.code reduct) := by
      apply Subtype.ext
      rw [shape]
      simp [applyRuleBindings, rootRule, applyBindings, numeralTerm]
    rw [← image]
    exact Relation.EqvGen.symm _ _ after

/-! ## The family of the tables whose rules determine their right sides -/

/-- **The family chosen from the step relations of the theories given by a
table whose rules determine their right sides**: the family of the listing of
their union. -/
noncomputable def determinedFamilyOfSpaces : Pattern → BasePremiseEvaluator :=
  listedFamily (unionListing determinedListing).code (unionListing determinedListing).next

/-- Each of its members respects the static equivalence, so each is a
presented candidate. -/
noncomputable def determinedMember (space : Pattern) : PresentedCandidate where
  presentation := ambientPresentation
  evaluator := determinedFamilyOfSpaces space
  respects := listedFamily_respectsStatics _ _ space

/-- **Each member of that family, the one at the empty space included, is a
host on terms of the theories given by a table whose rules determine their
right sides.** -/
theorem determinedFamily_hostOf_determinedTabular (space : Pattern) :
    (determinedMember space).Hosts DeterminedTabularTheory .terms .hosting := by
  rintro reading ⟨source, ⟨theory, table, tabular, determined, rfl⟩, interface, rfl⟩
  let member : ContextMap ((rewritingTheory theory).gslt interface).termsAlone
      (determinedFamily (tableCode table)).termsAlone :=
    ContextMap.ofTerms (source := (rewritingTheory theory).gslt interface)
      (target := (determinedFamily (tableCode table)).termsAlone) PUnit.unit
      (fun term => (term : LF.Term)) (fun related => related)
  have memberHosting : member.Hosting :=
    (ContextMap.ofTerms_hosting_iff (source := (rewritingTheory theory).gslt interface)
      (target := (determinedFamily (tableCode table)).termsAlone) PUnit.unit
      (fun term => (term : LF.Term)) (fun related => related)).mpr
      ⟨fun _ _ same => same,
        fun _ _ step => (determinedFamily_step tabular determined).mpr step,
        fun _ next step => ⟨next, (determinedFamily_step tabular determined).mp step, rfl⟩⟩
  exact ⟨((listedMap (unionListing determinedListing) space).comp
      (PrimeCandidate.memberMap determinedListing (tableCode table))).comp member,
    ((listedMap_hosting (unionListing determinedListing) space).comp
      (PrimeCandidate.memberMap_hosting determinedListing (tableCode table))).comp memberHosting⟩

/-- In particular of the class that the family of this delivery hosts at the
spaces of the tables. -/
theorem determinedFamily_hostOf_firstOrderTabular (space : Pattern) :
    (determinedMember space).Hosts FirstOrderTabular .terms .hosting :=
  HostOf.mono (determinedFamily_hostOf_determinedTabular space) fun _ member => member.determined

/-- **Negative**: that family does not take its rules from the space. -/
theorem determinedFamily_not_rulesFromSpace : ¬ FamilyRulesFromSpace determinedFamilyOfSpaces :=
  listedFamily_not_rulesFromSpace (unionListing determinedListing)
    (term := ⟨0, selfIdentity⟩) (reduct := ⟨0, identityTerm⟩)
    (UnionStep.member (selfIdentity_step _))

/-- **What separates the two families.**  Both have members that are
presented candidates; the family chosen from the sources hosts, at the empty
space, the class that the family that matches in its space hosts at the
spaces of the tables; the second takes its rules from the space and the first
does not. -/
theorem rulesFromSpace_separates :
    FamilyRulesFromSpace ambientEvaluator ∧
      ¬ FamilyRulesFromSpace determinedFamilyOfSpaces ∧
        (determinedMember emptySpace).Hosts FirstOrderTabular .terms .hosting ∧
          ∀ target : Contexts.Term ambient AtomsReduce.closedAtom,
            ¬ (ambientTheory emptySpaceTerm).rewrites (atomTerm 0 coin) target :=
  ⟨ambientEvaluator_rulesFromSpace, determinedFamily_not_rulesFromSpace,
    determinedFamily_hostOf_firstOrderTabular emptySpace, emptyMember_choice_normal⟩

#print axioms ambientEvaluator_rulesFromSpace
#print axioms rulesFromSpace_of_family
#print axioms matchingEvaluator_rulesFromSpace_of_family
#print axioms listedFamily_respectsStatics
#print axioms listedFamily_not_rulesFromSpace
#print axioms numeral_stepAt_inv
#print axioms listedMap_hosting
#print axioms determinedMember
#print axioms determinedFamily_hostOf_determinedTabular
#print axioms determinedFamily_hostOf_firstOrderTabular
#print axioms determinedFamily_not_rulesFromSpace
#print axioms rulesFromSpace_separates

end Mettapedia.Logic.HostingStyles.AmbientSpace
