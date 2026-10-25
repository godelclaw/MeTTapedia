import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.LiteralConstants

/-!
# Transport through renaming declared constants

A primitive renaming of rule presentations preserves declaration lookup,
universe rules and root computation. Its action keeps scoped variables and
head syntax fixed while renaming declared constants. Raw computation,
conversion and formation-sensitive typing respect this same action.
Reflection additionally requires a reverse primitive map and a left inverse
on names. Identifying source constants forces their mapped declaration types
to agree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type} {n m : Nat}

theorem StepCore.mapConst {source target : Rules Head} {names : DeclName → DeclName}
    (morphism : TypedEquality.RulesRenaming source target names)
    {left right : Tm Head n} (step : Step source.headEq left right source.computation) :
    Step target.headEq (left.mapConst names) (right.mapConst names) target.computation := by
  induction step with
  | betaPi body argument =>
      simpa only [Tm.mapConst, Tm.mapConst_inst0] using
        (Step.betaPi (headEq := target.headEq) (body.mapConst names) (argument.mapConst names))
  | betaSigmaFst first second => exact .betaSigmaFst _ _
  | betaSigmaSnd first second => exact .betaSigmaSnd _ _
  | head equality => exact .head (morphism.headEq equality)
  | root computation => exact .root (morphism.computation computation)
  | congPiDom step ih => exact .congPiDom ih
  | congPiCod step ih => exact .congPiCod ih
  | congSigmaDom step ih => exact .congSigmaDom ih
  | congSigmaCod step ih => exact .congSigmaCod ih
  | congIdTy step ih => exact .congIdTy ih
  | congIdLeft step ih => exact .congIdLeft ih
  | congIdRight step ih => exact .congIdRight ih
  | congLam step ih => exact .congLam ih
  | congAppFun step ih => exact .congAppFun ih
  | congAppArg step ih => exact .congAppArg ih
  | congPairFst step ih => exact .congPairFst ih
  | congPairSnd step ih => exact .congPairSnd ih
  | congFst step ih => exact .congFst ih
  | congSnd step ih => exact .congSnd ih
  | congRefl step ih => exact .congRefl ih

theorem Conv.mapConst {source target : Rules Head} {names : DeclName → DeclName}
    (morphism : TypedEquality.RulesRenaming source target names)
    {left right : Tm Head n} (conversion : Conv source.headEq left right source.computation) :
    Conv target.headEq (left.mapConst names) (right.mapConst names) target.computation := by
  induction conversion with
  | rel left right step => exact .rel _ _ (step.mapConst morphism)
  | refl term => exact .refl _
  | symm left right conversion ih => exact .symm _ _ ih
  | trans left middle right first second ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

theorem HasType.mapConst {source target : Rules Head} {names : DeclName → DeclName}
    (morphism : TypedEquality.RulesRenaming source target names)
    {context : Ctx Head n} {term type : Tm Head n} (typing : HasType source context term type) :
    HasType target (context.mapConst names) (term.mapConst names) (type.mapConst names) := by
  induction typing with
  | headType typed => exact .headType (morphism.headTyping typed)
  | @var n context index =>
      simpa only [Tm.mapConst, Ctx.lookup_mapConst] using
        (HasType.var (R := target) (Γ := context.mapConst names) index)
  | @const n context name type known =>
      simpa only [Tm.mapConst, Tm.mapConst_liftClosed] using
        (HasType.const (R := target) (Γ := context.mapConst names) (morphism.constantType known))
  | piForm _ universeA _ universeB join ihA ihB =>
      exact .piForm ihA (morphism.isUniverse universeA) ihB (morphism.isUniverse universeB) (morphism.join join)
  | sigmaForm _ universeA _ universeB join ihA ihB =>
      exact .sigmaForm ihA (morphism.isUniverse universeA) ihB (morphism.isUniverse universeB) (morphism.join join)
  | lamIntro _ ihBody => exact .lamIntro ihBody
  | appElim _ _ ihFunction ihArgument =>
      simpa only [Tm.mapConst, Tm.mapConst_inst0] using (HasType.appElim ihFunction ihArgument)
  | pairIntro _ _ ihFirst ihSecond =>
      rw [Tm.mapConst_inst0] at ihSecond
      exact .pairIntro ihFirst ihSecond
  | fstElim _ ihPair => exact .fstElim ihPair
  | sndElim _ ihPair =>
      simpa only [Tm.mapConst, Tm.mapConst_inst0] using (HasType.sndElim ihPair)
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      exact .idForm ihA (morphism.isUniverse universeWitness) ihLeft ihRight
  | reflIntro _ ihTerm => exact .reflIntro ihTerm
  | cumul _ order ihTerm => exact .cumul ihTerm (morphism.cumulative order)
  | conv _ conversion ihTerm => exact .conv ihTerm (conversion.mapConst morphism)

namespace FormationSensitive

theorem Typing.mapConst {source target : Rules Head} {names : DeclName → DeclName}
    (morphism : TypedEquality.RulesRenaming source target names)
    {context : Ctx Head n} {term type : Tm Head n} (typing : Typing source context term type) :
    Typing target (context.mapConst names) (term.mapConst names) (type.mapConst names) := by
  induction typing with
  | headType head => exact .headType (morphism.headTyping head)
  | @var n context index =>
      simpa only [Tm.mapConst, Ctx.lookup_mapConst] using
        (Typing.var (R := target) (Γ := context.mapConst names) index)
  | const known _ universeWitness ihType =>
      simpa only [Tm.mapConst, Tm.mapConst_liftClosed] using
        (Typing.const (morphism.constantType known) ihType (morphism.isUniverse universeWitness))
  | piForm _ universeA _ universeB join ihA ihB =>
      exact .piForm ihA (morphism.isUniverse universeA) ihB (morphism.isUniverse universeB) (morphism.join join)
  | sigmaForm _ universeA _ universeB join ihA ihB =>
      exact .sigmaForm ihA (morphism.isUniverse universeA) ihB (morphism.isUniverse universeB) (morphism.join join)
  | lamIntro _ universeWitness _ ihPi ihBody =>
      exact .lamIntro ihPi (morphism.isUniverse universeWitness) ihBody
  | appElim _ _ ihFunction ihArgument =>
      simpa only [Tm.mapConst, Tm.mapConst_inst0] using (Typing.appElim ihFunction ihArgument)
  | pairIntro _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      rw [Tm.mapConst_inst0] at ihSecond
      exact .pairIntro ihSigma (morphism.isUniverse universeWitness) ihFirst ihSecond
  | fstElim _ ihPair => exact .fstElim ihPair
  | sndElim _ ihPair =>
      simpa only [Tm.mapConst, Tm.mapConst_inst0] using (Typing.sndElim ihPair)
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      exact .idForm ihA (morphism.isUniverse universeWitness) ihLeft ihRight
  | reflIntro _ ihTerm => exact .reflIntro ihTerm
  | cumul _ order ihTerm => exact .cumul ihTerm (morphism.cumulative order)
  | conv _ _ universeWitness conversion ihTerm ihTarget =>
      exact .conv ihTerm ihTarget (morphism.isUniverse universeWitness) (conversion.mapConst morphism)

theorem ContextFormation.mapConst {source target : Rules Head} {names : DeclName → DeclName}
    (morphism : TypedEquality.RulesRenaming source target names)
    {context : Ctx Head n} (formed : ContextFormation source context) :
    ContextFormation target (context.mapConst names) := by
  induction formed with
  | nil => exact .nil
  | snoc _ typed universeWitness ih =>
      exact .snoc ih (typed.mapConst morphism) (morphism.isUniverse universeWitness)

theorem Judgment.mapConst {source target : Rules Head} {names : DeclName → DeclName}
    (morphism : TypedEquality.RulesRenaming source target names)
    {context : Ctx Head n} {term type : Tm Head n} (typed : Judgment source context term type) :
    Judgment target (context.mapConst names) (term.mapConst names) (type.mapConst names) :=
  ⟨typed.context.mapConst morphism, typed.typing.mapConst morphism⟩

theorem CtxMor.mapConst {source target : Rules Head} {names : DeclName → DeclName}
    (morphism : TypedEquality.RulesRenaming source target names)
    {context : Ctx Head n} {replacement : Ctx Head m} {substitution : Sub Head n m}
    (typed : CtxMor source context replacement substitution) :
    CtxMor target (context.mapConst names) (replacement.mapConst names)
      (fun index => (substitution index).mapConst names) := by
  intro index
  simpa only [Ctx.lookup_mapConst, Tm.mapConst_subst] using (typed index).mapConst morphism

theorem Judgment.mapConst_iff {source target : Rules Head} {names undo : DeclName → DeclName}
    (forward : TypedEquality.RulesRenaming source target names)
    (backward : TypedEquality.RulesRenaming target source undo)
    (inverse : ∀ name, undo (names name) = name)
    {context : Ctx Head n} {term type : Tm Head n} :
    Judgment source context term type ↔
      Judgment target (context.mapConst names) (term.mapConst names) (type.mapConst names) := by
  constructor
  · exact Judgment.mapConst forward
  · intro result
    have restored := result.mapConst backward
    simp only [Ctx.mapConst_mapConst, Tm.mapConst_mapConst] at restored
    have identity : (fun name => undo (names name)) = (fun name => name) := funext inverse
    rw [identity, Ctx.mapConst_id, Tm.mapConst_id, Tm.mapConst_id] at restored
    exact restored

end FormationSensitive

namespace TypedEquality.RulesRenaming

theorem identified_types {source target : Rules Head} {names : DeclName → DeclName}
    (morphism : TypedEquality.RulesRenaming source target names)
    {left right : DeclName} {leftType rightType : Tm Head 0}
    (leftKnown : source.constantType left = some leftType)
    (rightKnown : source.constantType right = some rightType)
    (identified : names left = names right) :
    leftType.mapConst names = rightType.mapConst names := by
  have first := morphism.constantType leftKnown
  have second := morphism.constantType rightKnown
  rw [identified] at first
  exact Option.some.inj (first.symm.trans second)

end TypedEquality.RulesRenaming

#print axioms StepCore.mapConst
#print axioms Conv.mapConst
#print axioms FormationSensitive.Typing.mapConst
#print axioms FormationSensitive.Judgment.mapConst
#print axioms TypedEquality.RulesRenaming.identified_types

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
