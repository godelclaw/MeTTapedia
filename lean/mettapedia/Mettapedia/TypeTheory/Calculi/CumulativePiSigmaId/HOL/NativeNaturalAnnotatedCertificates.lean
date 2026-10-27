import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedReindexing
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionElaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationConversionSubstitution

/-!
# Original structural certificates of interpreted natural conversion trees

The original declaration decoder receives the actual declared-row wrapper,
row ordinal and erased caller assignments. Beta uses its existing structural
code. Thus one typed tree has a source certificate checked by the maintained
decoder as well as its independently constructed retained HOL proof.

This emits certificates for the interpreted beta/natural-row fragment. Coverage
of arbitrary incoming structural certificates and contextual congruences is a
separate obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.SourceCertificates

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
    {operations : Operations Base Const} {profile enabled : Programs.ComputationProfiles.Selection}

abbrev RootCode (n : Nat) :=
  DeclarationConversionCode.RootCode (fun _ => Empty) (SchemaTableConversionCode.Code Tower.Head) n

abbrev Code (n : Nat) := StructuralConversionCode.Code Tower.Head RootCode n

def rootCode {row : Row} {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
    (inst : Instance operations profile row Γ context) : RootCode Γ.length := by
  cases row with
  | zero => exact .declared (SchemaTableConversionCode.encode Checking.table ⟨0, by decide⟩
      (CTm.eraseSub inst.sourceSubstitution))
  | successor => exact .declared (SchemaTableConversionCode.encode Checking.table ⟨1, by decide⟩
      (CTm.eraseSub inst.sourceSubstitution))

theorem rootCode_accepted {row : Row} {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
    (inst : Instance operations profile row Γ context) (selected : Programs.ComputationProfiles.Selection)
    (permitted : selected row.address = true) :
    (Programs.ComputationProfiles.decoder selected).decode (rootCode inst) =
      some (inst.source.term.erase, inst.target.term.erase) := by
  cases row with
  | zero =>
      simpa only [rootCode, Programs.ComputationProfiles.decoder, DeclarationConversionCode.rootDecoder,
        DeclarationConversionCode.decode, SchemaTableConversionCode.rootDecoder,
        Instance.source, Instance.target, Row.left, Row.right, CTm.erase_subst, erase_liftTm, SchemaTableConversionCode.encode] using
        SchemaTableConversionCode.decode_at Checking.table selected ⟨0, by decide⟩ permitted
          (left := natZeroIotaLeft) (right := natZeroIotaRight) rfl (CTm.eraseSub inst.sourceSubstitution)
  | successor =>
      simpa only [rootCode, Programs.ComputationProfiles.decoder, DeclarationConversionCode.rootDecoder,
        DeclarationConversionCode.decode, SchemaTableConversionCode.rootDecoder,
        Instance.source, Instance.target, Row.left, Row.right, CTm.erase_subst, erase_liftTm, SchemaTableConversionCode.encode] using
        SchemaTableConversionCode.decode_at Checking.table selected ⟨1, by decide⟩ permitted
          (left := natSuccIotaLeft) (right := natSuccIotaRight) rfl (CTm.eraseSub inst.sourceSubstitution)

def stepCode : {index : Index Base} → {source target : State operations profile index} →
    Step operations profile enabled source target → StructuralConversionCode.StepCode Tower.Head RootCode index.targetContext.length
  | _, _, _, .row inst _ _ => .root (rootCode inst)
  | _, _, _, .beta inst => .betaPi inst.body.erase inst.argument.erase

theorem beta_accepted {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
    (inst : BetaInstance operations profile Γ context) (selected : Programs.ComputationProfiles.Selection) :
    (StructuralConversionCode.StepCode.betaPi inst.body.erase inst.argument.erase).check Tower.rules.headEq
      (Programs.ComputationProfiles.decoder selected).decode inst.source.term.erase inst.target.term.erase = true := by
  simp [StructuralConversionCode.StepCode.check, StructuralConversionCode.StepCode.decode,
    BetaInstance.source, BetaInstance.target, CTm.erase, CTm.erase_inst0]

theorem step_accepted {index : Index Base} {source target : State operations profile index}
    (step : Step operations profile enabled source target) :
    (stepCode step).check Tower.rules.headEq (Programs.ComputationProfiles.decoder profile).decode
      source.term.erase target.term.erase = true := by
  cases step with
  | row inst inProfile _ => exact decide_eq_true (rootCode_accepted inst profile inProfile)
  | beta inst => exact beta_accepted inst profile

theorem step_selected {index : Index Base} {source target : State operations profile index}
    (step : Step operations profile enabled source target) :
    (stepCode step).check Tower.rules.headEq (Programs.ComputationProfiles.decoder enabled).decode
      source.term.erase target.term.erase = true := by
  cases step with
  | row inst _ permitted => exact decide_eq_true (rootCode_accepted inst enabled permitted)
  | beta inst => exact beta_accepted inst enabled

def equality (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection) :
    (bubbles operations profile).GlobalEquality :=
  StructuralConversionCode.Elaboration.equality (bubbles operations profile)
    (fun index => index.targetContext.length) (fun state => state.term.erase)
    Tower.rules.headEq (Programs.ComputationProfiles.decoder profile).decode

def certificate {index : Index Base} {source target : State operations profile index}
    (step : Step operations profile enabled source target) : (equality operations profile).Eq source target :=
  StructuralConversionCode.Certificate.single (stepCode step) (step_accepted step)

def emit {index : Index Base} {source target : State operations profile index}
    (path : (bubbles operations profile).Conv enabled source target) :
    StructuralConversionCode.Certificate Tower.rules.headEq (Programs.ComputationProfiles.decoder profile).decode
      source.term.erase target.term.erase :=
  StructuralConversionCode.Elaboration.emit (B := bubbles operations profile)
    (arity := fun index => index.targetContext.length) (readout := fun state => state.term.erase)
    certificate path

theorem emit_selected {index : Index Base} {source target : State operations profile index}
    (path : (bubbles operations profile).Conv enabled source target) :
    (emit path).code.check Tower.rules.headEq (Programs.ComputationProfiles.decoder enabled).decode
      source.term.erase target.term.erase = true := by
  exact StructuralConversionCode.Elaboration.checkWith (B := bubbles operations profile) (RootCode := RootCode)
    (arity := fun index => index.targetContext.length) (readout := fun state => state.term.erase)
    (certificate (enabled := enabled)) Tower.rules.headEq (Programs.ComputationProfiles.decoder enabled).decode
    (fun step => step_selected step) path

local instance (profile : Programs.ComputationProfiles.Selection) :
    DecidableRel (Programs.ComputationProfiles.rules profile).headEq :=
  fun left right => inferInstanceAs (Decidable (Tower.rules.headEq left right))

theorem emit_original {index : Index Base} {source target : State operations profile index}
    (path : (bubbles operations profile).Conv enabled source target) :
    Conv (Programs.ComputationProfiles.rules profile).headEq source.term.erase target.term.erase
      (Programs.ComputationProfiles.rules profile).computation :=
  StructuralConversionCode.Code.check_sound (Programs.ComputationProfiles.decoder profile) (emit path).checked

theorem emit_work {index : Index Base} {source target : State operations profile index}
    (path : (bubbles operations profile).Conv enabled source target) :
    (emit path).code.stepCount = BubbleElaboration.stepCount path :=
  StructuralConversionCode.Elaboration.stepCount (B := bubbles operations profile)
    (arity := fun index => index.targetContext.length) (readout := fun state => state.term.erase)
    (certificate (enabled := enabled)) (fun _ => rfl) path

theorem certificate_widen {large : Programs.ComputationProfiles.Selection}
    (included : ∀ row, enabled row = true → large row = true)
    {index : Index Base} {source target : State operations profile index}
    (step : Step operations profile enabled source target) :
    certificate (step.widen included) = certificate step := by
  cases step <;> rfl

theorem emit_widen {large : Programs.ComputationProfiles.Selection}
    (included : ∀ row, enabled row = true → large row = true)
    {index : Index Base} {source target : State operations profile index}
    (path : (bubbles operations profile).Conv enabled source target) :
    emit ((bubbles operations profile).widen (Step.widen included) path) = emit path :=
  BubbleElaboration.sound_widen (bubbles operations profile) (equality operations profile)
    (Step.widen included) certificate certificate (certificate_widen included) path

def substituteRoot {n m : Nat} (substitution : Sub Tower.Head n m) (code : RootCode n) : RootCode m :=
  DeclarationConversionCode.RootCode.substitute (fun _ code => Empty.elim code)
    SchemaTableConversionCode.Code.substitute substitution code

theorem decode_substitute (selected : Programs.ComputationProfiles.Selection)
    {n m : Nat} (substitution : Sub Tower.Head n m) (code : RootCode n) :
    (Programs.ComputationProfiles.decoder selected).decode (substituteRoot substitution code) =
      ((Programs.ComputationProfiles.decoder selected).decode code).map
        (fun endpoints => (subst substitution endpoints.1, subst substitution endpoints.2)) := by
  simpa only [Programs.ComputationProfiles.decoder, DeclarationConversionCode.rootDecoder,
    SchemaTableConversionCode.rootDecoder, StructuralConversionCode.RootDecoder.ofEmpty, substituteRoot] using
    DeclarationConversionCode.decode_substitute (fun _ code => Empty.elim code)
      SchemaTableConversionCode.Code.substitute (Programs.ComputationProfiles.signature selected)
      (StructuralConversionCode.RootDecoder.ofEmpty Tower.rules.computation rfl).decode
      (SchemaTableConversionCode.decode Checking.table selected)
      (fun _ code => nomatch code) (SchemaTableConversionCode.decode_substitute Checking.table selected)
      substitution code

theorem stepCode_castType {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
    {firstType secondType : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    (same : firstType = secondType)
    {source target : State operations profile ⟨Γ, context, firstType, carrier⟩}
    (step : Step operations profile enabled source target) : stepCode (step.castType same) = stepCode step := by
  cases same
  rfl

theorem stepCode_castStates {index : Index Base}
    {source target source' target' : State operations profile index}
    (left : source = source') (right : target = target')
    (step : Step operations profile enabled source target) :
    stepCode (step.castStates left right) = stepCode step := by
  cases left
  cases right
  rfl

variable {Γ Ξ : HOL.Ctx Base} {sourceContext : CCtx Tower.Head Γ.length}
    {targetContext : CCtx Tower.Head Ξ.length}
    (substitution : Substitution operations profile Γ Ξ sourceContext targetContext)

theorem rootCode_substitute {row : Row} (inst : Instance operations profile row Γ sourceContext) :
    rootCode (substitution.instantiate inst) = substituteRoot (CTm.eraseSub substitution.source) (rootCode inst) := by
  cases row <;>
    simp only [rootCode, Substitution.instantiate, substituteRoot, DeclarationConversionCode.RootCode.substitute,
      SchemaTableConversionCode.encode, SchemaTableConversionCode.Code.substitute,
      SchemaTableConversionCode.Code.mapArguments, List.map_ofFn, Function.comp_def]
  all_goals
    congr 3
    funext index
    exact CTm.erase_subst substitution.source (inst.sourceSubstitution index)

variable [DecidableEq Base]

theorem stepCode_substitute {type : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    {source target : State operations profile ⟨Γ, sourceContext, type, carrier⟩}
    (step : Step operations profile enabled source target) :
    stepCode (substitution.step step) = (stepCode step).substitute substituteRoot (CTm.eraseSub substitution.source) := by
  cases step with
  | row inst inProfile permitted =>
      change stepCode (((Step.row (enabled := enabled) (substitution.instantiate inst) inProfile permitted).castType
        (substitution.row_type inst)).castStates (substitution.row_source inst) (substitution.row_target inst)) = _
      rw [stepCode_castStates, stepCode_castType]
      change StructuralConversionCode.StepCode.root (rootCode (substitution.instantiate inst)) =
        .root (substituteRoot (CTm.eraseSub substitution.source) (rootCode inst))
      rw [rootCode_substitute]
  | beta inst =>
      have lifted : CTm.eraseSub (CTm.liftSub substitution.source) =
          Presentation.liftSub (CTm.eraseSub substitution.source) :=
        funext (CTm.eraseSub_liftSub substitution.source)
      change stepCode (((Step.beta (enabled := enabled) (substitution.beta inst)).castType
        (substitution.beta_type inst)).castStates (substitution.beta_source inst) (substitution.beta_target inst)) = _
      rw [stepCode_castStates, stepCode_castType]
      simp only [stepCode, Substitution.beta, CTm.erase_subst, StructuralConversionCode.StepCode.substitute, lifted]

/-- The context map agrees on the full submitted source code, as well as
on the independently constructed HOL proof. -/
theorem emit_substitute {type : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    {source target : State operations profile ⟨Γ, sourceContext, type, carrier⟩}
    (path : (bubbles operations profile).Conv enabled source target) :
    (emit ((substitution.fibreMap enabled type carrier).mapConv path)).code =
      (emit path).code.substitute substituteRoot (CTm.eraseSub substitution.source) := by
  apply StructuralConversionCode.Elaboration.substitute (B := bubbles operations profile)
    (arity := fun index => index.targetContext.length) (readout := fun state => state.term.erase)
    certificate substituteRoot (substitution.fibreMap enabled type carrier)
    (CTm.eraseSub substitution.source) (fun state => CTm.erase_subst substitution.source state.term) ?_ path
  intro source target step
  simp only [certificate, StructuralConversionCode.Certificate.single, Substitution.fibreMap,
    stepCode_substitute, StructuralConversionCode.Code.substitute]

#print axioms rootCode_accepted
#print axioms emit_selected
#print axioms emit_original
#print axioms emit_work
#print axioms emit_widen
#print axioms decode_substitute
#print axioms emit_substitute

end AnnotatedConversion.SourceCertificates
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
