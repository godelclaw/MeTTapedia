import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveCheckingOSLF

/-!
# Native types of supplied, formation-preserving dependent steps

The original directional structural relation supplies the OSLF diamond. Its
postcondition retains an exact target and the original formed typing judgment.
Finite evidence checks the source, selected step and target independently.
Rejecting one evidence package is not a proof that no package can exist.

This is a workload-level consumer of the existing dependent checker, not a
generic algorithm for extracting a minimal rule package or qualifying every
computation in a restricted theory.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.DependentChecking

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT

variable {Head : Type} {n : Nat}

/-- The evaluator-facing observation uses forward steps, not conversion. -/
abbrev theory (R : Rules Head) (n : Nat) : GSLT :=
  equalityGSLT (Tm Head n) (fun source target =>
    Step R.headEq source target R.computation)

/-- A formed source can take a selected step to the same type at the exact
requested endpoint. Target formation is not inferred from conversion. -/
def nativeType (R : Rules Head) (context : Ctx Head n) (type target : Tm Head n) :
    GSLTNativeType (theory R n) where
  sort := ()
  pred := ⟨fun source => FormationSensitive.Judgment R context source type ∧
      semanticDiamond (theory R n)
        (saturatePredicate (theory R n) (fun candidate =>
          candidate = target ∧ FormationSensitive.Judgment R context candidate type)) source,
    by
      intro left right same
      change left = right at same
      cases same
      rfl⟩

theorem native_exact (R : Rules Head) (context : Ctx Head n)
    (source target type : Tm Head n) :
    (gsltOSLF (theory R n)).satisfies (S := ()) source
      (nativeType R context type target).pred ↔
      FormationSensitive.Judgment R context source type ∧
        Step R.headEq source target R.computation ∧
          FormationSensitive.Judgment R context target type := by
  change (_ ∧ gsltDiamond (theory R n) _ source) ↔ _
  constructor
  · rintro ⟨formed, member⟩
    obtain ⟨candidate, step, observed⟩ :=
      (gsltDiamond_spec (theory R n) _ source).mp member
    have endpoint := (saturatePredicate_apply_iff_of_equiv_iff_eq
      (theory R n) (fun _ _ => Iff.rfl) _ candidate).mp observed
    rcases endpoint with ⟨rfl, typed⟩
    exact ⟨formed, step, typed⟩
  · rintro ⟨formed, step, typed⟩
    refine ⟨formed, (gsltDiamond_spec (theory R n) _ source).mpr ?_⟩
    exact ⟨target, step,
      (saturatePredicate_apply_iff_of_equiv_iff_eq
        (theory R n) (fun _ _ => Iff.rfl) _ target).mpr ⟨rfl, typed⟩⟩

section Checking

variable {R : Rules Head} [DecidableEq Head] [DecidableRel R.headTyping]
    [DecidablePred R.isUniverse] [∀ u v w, Decidable (R.join u v w)]
    [DecidableRel R.cumulative] [DecidableRel R.headEq]

structure Certificate (decoder : StructuralConversionCode.RootDecoder R.computation)
    (context : Ctx Head n) (source target type : Tm Head n) where
  source : FormationSensitiveChecking.Request decoder
    (FormationSensitiveRuleSignature.judgment context source type)
  step : StructuralConversionCode.StepCode Head decoder.Code n
  target : FormationSensitiveChecking.Request decoder
    (FormationSensitiveRuleSignature.judgment context target type)

def Certificate.check (decoder : StructuralConversionCode.RootDecoder R.computation)
    {context : Ctx Head n} {source target type : Tm Head n}
    (certificate : Certificate decoder context source target type) : Bool :=
  certificate.source.check decoder &&
    certificate.step.check R.headEq decoder.decode source target &&
      certificate.target.check decoder

theorem Certificate.sound (decoder : StructuralConversionCode.RootDecoder R.computation)
    {context : Ctx Head n} {source target type : Tm Head n}
    (certificate : Certificate decoder context source target type)
    (accepted : certificate.check decoder = true) :
    (gsltOSLF (theory R n)).satisfies (S := ()) source
      (nativeType R context type target).pred := by
  simp only [Certificate.check, Bool.and_eq_true] at accepted
  exact (native_exact R context source target type).mpr
    ⟨certificate.source.sound decoder accepted.1.1,
      StructuralConversionCode.StepCode.check_sound decoder accepted.1.2,
      certificate.target.sound decoder accepted.2⟩

/-- Completeness concerns existence of finite supplied evidence, not search. -/
theorem native_iff_certificate (decoder : StructuralConversionCode.RootDecoder R.computation)
    (context : Ctx Head n) (source target type : Tm Head n) :
    (gsltOSLF (theory R n)).satisfies (S := ()) source
      (nativeType R context type target).pred ↔
      ∃ certificate : Certificate decoder context source target type,
        certificate.check decoder = true := by
  constructor
  · intro member
    obtain ⟨sourceTyped, step, targetTyped⟩ :=
      (native_exact R context source target type).mp member
    obtain ⟨sourceContext, sourceNodes, sourceRoot, sourceAccepted⟩ :=
      (FormationSensitiveChecking.judgment_iff_checked decoder
        (FormationSensitiveRuleSignature.judgment context source type)).mp sourceTyped
    obtain ⟨targetContext, targetNodes, targetRoot, targetAccepted⟩ :=
      (FormationSensitiveChecking.judgment_iff_checked decoder
        (FormationSensitiveRuleSignature.judgment context target type)).mp targetTyped
    obtain ⟨stepCode, stepAccepted⟩ :=
      (StructuralConversionCode.StepCode.step_iff_checked decoder).mp step
    exact ⟨⟨⟨sourceContext, sourceNodes, sourceRoot⟩, stepCode,
      ⟨targetContext, targetNodes, targetRoot⟩⟩,
      by simp [Certificate.check, FormationSensitiveChecking.Request.check,
        sourceAccepted, targetAccepted, stepAccepted]⟩
  · rintro ⟨certificate, accepted⟩
    exact certificate.sound decoder accepted

/-- Exhausting a finite list of supplied packages rejects those packages;
the theorem makes no assertion about unsupplied proofs. -/
def checkWorkload (decoder : StructuralConversionCode.RootDecoder R.computation)
    (workload : List ((n : Nat) × (context : Ctx Head n) ×
      (source : Tm Head n) × (target : Tm Head n) × (type : Tm Head n) ×
        Certificate decoder context source target type)) : Bool :=
  workload.all fun entry => entry.2.2.2.2.2.check decoder

theorem checkWorkload_sound (decoder : StructuralConversionCode.RootDecoder R.computation)
    (workload : List ((n : Nat) × (context : Ctx Head n) ×
      (source : Tm Head n) × (target : Tm Head n) × (type : Tm Head n) ×
        Certificate decoder context source target type))
    (checked : checkWorkload decoder workload = true) :
    ∀ entry ∈ workload,
      (gsltOSLF (theory R entry.1)).satisfies (S := ()) entry.2.2.1
        (nativeType R entry.2.1 entry.2.2.2.2.1 entry.2.2.2.1).pred := by
  intro entry member
  exact entry.2.2.2.2.2.sound decoder
    ((List.all_eq_true.mp checked) entry member)

end Checking

end Mettapedia.OSLF.NativeTypes.Consumers.DependentChecking
