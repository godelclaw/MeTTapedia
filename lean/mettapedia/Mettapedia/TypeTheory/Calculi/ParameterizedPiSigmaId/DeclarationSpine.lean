import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypingGeneration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction

/-!
# Declared application spines for the raw typing judgment

The declared head fixes a principal type. Existing raw generation and the
Pi conversion boundary recover the dependent arguments and retain the
observed conversion/cumulativity tail. No context-formation premise or
raw-to-formation-sensitive upgrade is used.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type} {R : Rules Head} {n k : Nat}

namespace HasType

private theorem constantAdjustmentAux {Γ : Ctx Head n} {term displayed : Tm Head n}
    (typing : HasType R Γ term displayed) :
    ∀ {name : DeclName} {declared : Tm Head 0}, term = .const name →
      R.constantType name = some declared →
        TypeAdjustment R (liftClosed declared) displayed := by
  induction typing with
  | const known =>
      intro name declared equality lookup
      cases equality
      rw [known] at lookup
      cases lookup
      exact .refl _
  | cumul _ order ih =>
      intro name declared equality lookup
      exact .trans (ih equality lookup) (.cumulative order)
  | conv _ conversion ih =>
      intro name declared equality lookup
      exact .trans (ih equality lookup) (.conversion conversion)
  | _ => intro name declared equality; cases equality

theorem constantAdjustment {Γ : Ctx Head n} {name : DeclName}
    {declared : Tm Head 0} {displayed : Tm Head n}
    (typing : HasType R Γ (.const name) displayed)
    (known : R.constantType name = some declared) :
    TypeAdjustment R (liftClosed declared) displayed :=
  constantAdjustmentAux typing rfl known

inductive DeclarationSpine (R : Rules Head) (Γ : Ctx Head n) :
    Tm Head n → Tm Head n → Prop where
  | constant {name : DeclName} {declared : Tm Head 0} :
      R.constantType name = some declared →
        DeclarationSpine R Γ (.const name) (liftClosed declared)
  | app {function argument domain : Tm Head n} {codomain : Tm Head (n + 1)} :
      DeclarationSpine R Γ function (.pi domain codomain) →
      HasType R Γ argument domain →
        DeclarationSpine R Γ (.app function argument) (inst0 argument codomain)

namespace DeclarationSpine

/-- An undeclared head cannot supply a declaration-rooted spine. Raw lambda
typing's omitted domain formation does not create a declaration lookup. -/
theorem missingConstant {Γ : Ctx Head n} {name : DeclName} {type : Tm Head n}
    (missing : R.constantType name = none) :
    ¬ DeclarationSpine R Γ (.const name) type := by
  intro spine
  cases spine with
  | constant known => rw [missing] at known; cases known

theorem typing {Γ : Ctx Head n} {term type : Tm Head n}
    (spine : DeclarationSpine R Γ term type) : HasType R Γ term type := by
  induction spine with
  | constant known => exact .const known
  | app _ argumentTyped ih => exact .appElim ih argumentTyped

theorem adjustment (boundary : PiConversionBoundary R)
    {Γ : Ctx Head n} {term type : Tm Head n}
    (spine : DeclarationSpine R Γ term type) :
    ∀ {displayed}, HasType R Γ term displayed → TypeAdjustment R type displayed := by
  induction spine with
  | constant known => intro displayed observed; exact observed.constantAdjustment known
  | @app function argument domain codomain previous argumentTyped ih =>
      intro displayed observed
      obtain ⟨_, _, observedFunction, _, resultAdjustment⟩ := observed.appGeneration
      have components := boundary.components ((ih observedFunction).toConvOfPiTarget boundary)
      exact .trans (.conversion (components.2.substitute (subst0 argument))) resultAdjustment

theorem recoverApplication (boundary : PiConversionBoundary R)
    {Γ : Ctx Head n} {function argument domain displayed : Tm Head n}
    {codomain : Tm Head (n + 1)}
    (spine : DeclarationSpine R Γ function (.pi domain codomain))
    (observed : HasType R Γ (.app function argument) displayed) :
    HasType R Γ argument domain ∧
      DeclarationSpine R Γ (.app function argument) (inst0 argument codomain) ∧
      TypeAdjustment R (inst0 argument codomain) displayed ∧
      (∀ {replacement}, HasType R Γ replacement (inst0 argument codomain) →
        HasType R Γ replacement displayed) := by
  obtain ⟨_, _, observedFunction, observedArgument, resultAdjustment⟩ := observed.appGeneration
  have components := boundary.components
    ((spine.adjustment boundary observedFunction).toConvOfPiTarget boundary)
  have argumentTyped : HasType R Γ argument domain :=
    .conv observedArgument (.symm _ _ components.1)
  have resultConversion := components.2.substitute (subst0 argument)
  exact ⟨argumentTyped, .app spine argumentTyped,
    .trans (.conversion resultConversion) resultAdjustment,
    fun replacement => (replacement.conv resultConversion).adjust resultAdjustment⟩

theorem replay (boundary : PiConversionBoundary R)
    {Γ : Ctx Head n} {term type displayed replacement : Tm Head n}
    (spine : DeclarationSpine R Γ term type) (observed : HasType R Γ term displayed)
    (replacementTyped : HasType R Γ replacement type) :
    HasType R Γ replacement displayed :=
  replacementTyped.adjust (spine.adjustment boundary observed)

open TelescopeAbstraction

theorem recoverTelescope (boundary : PiConversionBoundary R)
    {Γ : Ctx Head n} (telescope : Ctx Head k) :
    ∀ (result : Tm Head k) (substitution : Sub Head k n)
      {function displayed : Tm Head n},
      DeclarationSpine R Γ function (liftClosed (closeType telescope result)) →
      HasType R Γ (applyClosed telescope substitution function) displayed →
      CtxMor R telescope Γ substitution ∧
        DeclarationSpine R Γ (applyClosed telescope substitution function)
          (subst substitution result) ∧
        TypeAdjustment R (subst substitution result) displayed ∧
        (∀ {replacement}, HasType R Γ replacement (subst substitution result) →
          HasType R Γ replacement displayed) := by
  induction telescope with
  | nil =>
      intro result substitution function displayed spine observed
      rw [subst_empty substitution result]
      exact ⟨(fun i => Fin.elim0 i), spine, spine.adjustment boundary observed,
        fun replacement => spine.replay boundary observed replacement⟩
  | @snoc k telescope domain ih =>
      intro result substitution function displayed spine observed
      obtain ⟨_, _, previousObserved, _, _⟩ := observed.appGeneration
      obtain ⟨previousTyped, previousSpine, _, _⟩ :=
        ih (.pi domain result) (fun i => substitution i.succ) spine previousObserved
      obtain ⟨argumentTyped, nextSpine, adjustment, replay⟩ :=
        previousSpine.recoverApplication boundary observed
      have opened : inst0 (substitution 0)
          (subst (liftSub (fun i => substitution i.succ)) result) =
          subst substitution result := by
        rw [← subst_consSub, consSub_eta]
      rw [opened] at nextSpine adjustment replay
      have typed := previousTyped.extend argumentTyped
      rw [consSub_eta] at typed
      exact ⟨typed, nextSpine, adjustment, replay⟩

end DeclarationSpine
end HasType

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
