import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement
import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# The reference relation modulo equations

A language's equations hold in every context and in both directions. The generators are:
- authored equation instances, scope-correct: an equation matches one side, its premises have
  witnesses, and the other side is instantiated with every value shifted from its capture depth
  (`AuthoredEquation`);
- the laws the presentation derives for its declared collections, exactly the canonical ones
  (`EquationSemantics.DerivedInstance`).

Closing the generators under one-hole contexts and under equivalence gives `Equivalent`. The reference
relation modulo equations takes one reference step between equivalent representatives (`StepModulo`).

On an aligned language whose equations are aligned (`EquationsAligned`: premises aligned, and no
metavariable deeper on the instantiated side than its capture depth), this is the canonical relation
modulo equations (`stepModuloEquations_iff`). On an equation-free language, equivalence is equality
(`equivalent_iff_eq_of_isEquationFree`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open Syntax Match Engine ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics
  (DerivedInstance StepModuloEquations EquationEquiv EquationContextStep EquationGenerator EquationInstance
    EquationInstanceAt)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)

variable (relEnv : RelationEnv) (language : LanguageDef)

/-- **An authored equation instance**: the equation matches the source by one side, its premises have
witnesses, and the target is the other side, instantiated scope-correctly. -/
inductive AuthoredEquation : Pattern → Pattern → Prop
  | forward {equation : Equation} {source : Pattern} {initial final : Bindings} {witnesses : List Witness} :
      equation ∈ language.equations →
      initial ∈ matchPattern equation.left source →
      PremisesValid relEnv language (captureSitesOf equation.left equation.premises) initial equation.premises
        witnesses final →
      AuthoredEquation source (applyBindingsScoped (captureSitesOf equation.left equation.premises) final 0
        equation.right)
  | reverse {equation : Equation} {source : Pattern} {initial final : Bindings} {witnesses : List Witness} :
      equation ∈ language.equations →
      initial ∈ matchPattern equation.right source →
      PremisesValid relEnv language (captureSitesOf equation.right equation.premises) initial equation.premises
        witnesses final →
      AuthoredEquation source (applyBindingsScoped (captureSitesOf equation.right equation.premises) final 0
        equation.left)

/-- One generator of the equations: an authored instance or a derived collection law. -/
def Generator (source target : Pattern) : Prop :=
  AuthoredEquation relEnv language source target ∨ DerivedInstance language source target

/-- One generator in one context. -/
inductive EquationStep : Pattern → Pattern → Prop
  | inContext (context : OneHoleContext) {redex contractum : Pattern} :
      Generator relEnv language redex contractum →
      EquationStep (context.fill redex) (context.fill contractum)

/-- **Equivalence modulo the equations.** -/
def Equivalent : Pattern → Pattern → Prop :=
  Relation.EqvGen (EquationStep relEnv language)

/-- **The reference relation modulo equations**: one reference step between equivalent representatives. -/
def StepModulo (source target : Pattern) : Prop :=
  ∃ redex contractum, Equivalent relEnv language source redex ∧ Step relEnv language redex contractum ∧
    Equivalent relEnv language contractum target

/-! ## Aligned equations -/

/-- **An equation both relations interpret alike**: its premises are aligned from either side, and
neither side holds a metavariable deeper than where the other side captured it. -/
def equationAligned (equation : Equation) : Bool :=
  equation.premises.all (premiseAligned (captureSitesOf equation.left equation.premises)) &&
    equation.premises.all (premiseAligned (captureSitesOf equation.right equation.premises)) &&
    notDeeper (captureSitesOf equation.left equation.premises) 0 equation.right &&
    notDeeper (captureSitesOf equation.right equation.premises) 0 equation.left

/-- Every equation of the language is aligned. -/
def EquationsAligned : Prop := ∀ equation ∈ language.equations, equationAligned equation = true

/-! ## Agreement -/

variable {relEnv language}

theorem equationAligned_parts {equation : Equation} (aligned : equationAligned equation = true) :
    (∀ premise ∈ equation.premises, premiseAligned (captureSitesOf equation.left equation.premises) premise = true) ∧
      (∀ premise ∈ equation.premises, premiseAligned (captureSitesOf equation.right equation.premises) premise = true) ∧
      notDeeper (captureSitesOf equation.left equation.premises) 0 equation.right = true ∧
      notDeeper (captureSitesOf equation.right equation.premises) 0 equation.left = true := by
  simp only [equationAligned, Bool.and_eq_true, List.all_eq_true] at aligned
  exact ⟨aligned.1.1.1, aligned.1.1.2, aligned.1.2, aligned.2⟩

/-- **On aligned equations, the authored instances are the canonical ones.** -/
theorem authoredEquation_iff (profile : ReferenceProfile language) (equations : EquationsAligned language)
    {source target : Pattern} :
    EquationInstance (engineBasePremises relEnv) language source target ↔
      AuthoredEquation relEnv language source target := by
  constructor
  · rintro ⟨fuel, instanceEvidence⟩
    cases instanceEvidence with
    | @forward equation _ _ initial final member matched premises targetEq =>
      obtain ⟨forwardPremises, -, forwardRight, -⟩ := equationAligned_parts (equations equation member)
      obtain ⟨witnesses, valid⟩ := premisesValid_of_premisesAt relEnv language profile forwardPremises premises
      have instantiated := applyBindingsScoped_eq_applyBindings_of_notDeeper
        (captureSitesOf equation.left equation.premises) final 0 equation.right forwardRight
      rw [← targetEq, ← instantiated]
      exact .forward member matched valid
    | @reverse equation _ _ initial final member matched premises targetEq =>
      obtain ⟨-, reversePremises, -, reverseLeft⟩ := equationAligned_parts (equations equation member)
      obtain ⟨witnesses, valid⟩ := premisesValid_of_premisesAt relEnv language profile reversePremises premises
      have instantiated := applyBindingsScoped_eq_applyBindings_of_notDeeper
        (captureSitesOf equation.right equation.premises) final 0 equation.left reverseLeft
      rw [← targetEq, ← instantiated]
      exact .reverse member matched valid
  · intro authored
    cases authored with
    | @forward equation _ initial final witnesses member matched valid =>
      obtain ⟨forwardPremises, -, forwardRight, -⟩ := equationAligned_parts (equations equation member)
      obtain ⟨fuel, premises⟩ := premisesAt_of_premisesValid relEnv language profile witnesses forwardPremises valid
      rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ final 0 equation.right forwardRight]
      exact ⟨fuel, .forward member matched premises rfl⟩
    | @reverse equation _ initial final witnesses member matched valid =>
      obtain ⟨-, reversePremises, -, reverseLeft⟩ := equationAligned_parts (equations equation member)
      obtain ⟨fuel, premises⟩ := premisesAt_of_premisesValid relEnv language profile witnesses reversePremises valid
      rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ final 0 equation.left reverseLeft]
      exact ⟨fuel, .reverse member matched premises rfl⟩

theorem generator_iff (profile : ReferenceProfile language) (equations : EquationsAligned language)
    {source target : Pattern} :
    EquationGenerator (engineBasePremises relEnv) language source target ↔ Generator relEnv language source target :=
  or_congr (authoredEquation_iff profile equations) Iff.rfl

theorem equationStep_iff (profile : ReferenceProfile language) (equations : EquationsAligned language)
    {source target : Pattern} :
    EquationContextStep (engineBasePremises relEnv) language source target ↔
      EquationStep relEnv language source target := by
  constructor
  · intro step
    cases step with
    | inContext context generator => exact .inContext context ((generator_iff profile equations).mp generator)
  · intro step
    cases step with
    | inContext context generator => exact .inContext context ((generator_iff profile equations).mpr generator)

/-- **On aligned equations, equivalence is the canonical equivalence.** -/
theorem equivalent_iff (profile : ReferenceProfile language) (equations : EquationsAligned language)
    {source target : Pattern} :
    EquationEquiv (engineBasePremises relEnv) language source target ↔ Equivalent relEnv language source target :=
  ⟨fun equivalent =>
      Relation.EqvGen.mono (fun _ _ step => (equationStep_iff profile equations).mp step) _ _ equivalent,
    fun equivalent =>
      Relation.EqvGen.mono (fun _ _ step => (equationStep_iff profile equations).mpr step) _ _ equivalent⟩

/-- **On an aligned language with aligned equations, the reference relation modulo equations is the
canonical one.** -/
theorem stepModuloEquations_iff (profile : ReferenceProfile language) (equations : EquationsAligned language)
    {source target : Pattern} :
    StepModuloEquations (engineBasePremises relEnv) language source target ↔
      StepModulo relEnv language source target := by
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    exact ⟨redex, contractum, (equivalent_iff profile equations).mp before,
      (contextualStep_iff_step relEnv language profile).mp step, (equivalent_iff profile equations).mp after⟩
  · rintro ⟨redex, contractum, before, step, after⟩
    exact ⟨redex, contractum, (equivalent_iff profile equations).mpr before,
      (contextualStep_iff_step relEnv language profile).mpr step, (equivalent_iff profile equations).mpr after⟩

/-! ## Equation-free languages -/

/-- **In an equation-free language, equivalence is equality**: it has no authored equations and no
collection laws. -/
theorem equivalent_iff_eq_of_isEquationFree (free : language.isEquationFree = true) {first second : Pattern} :
    Equivalent relEnv language first second ↔ first = second := by
  constructor
  · intro equivalent
    induction equivalent with
    | rel _ _ step =>
      cases step with
      | inContext context generator =>
        rcases generator with authored | derived
        · cases authored <;>
            simp_all [Mettapedia.GSLT.LanguageDef.EquationSemantics.equations_eq_nil_of_isEquationFree free]
        · exact absurd derived
            (Mettapedia.GSLT.LanguageDef.EquationSemantics.no_derivedInstance_of_isEquationFree free _ _)
    | refl => rfl
    | symm _ _ _ same => exact same.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  · rintro rfl
    exact Relation.EqvGen.refl _

end Mettapedia.OSLF.MeTTaIL.ReferenceStep
